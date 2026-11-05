import Netlib.Import.NftablesICMPControl

namespace NetlibTest.NftablesICMPControl

open Netlib Packet Import.NftablesICMPControl

private def nativeJSON : String := r#"{"nftables": [{"metainfo": {"version": "1.1.3", "release_name": "Commodore Bullmoose #4", "json_schema_version": 1}}, {"table": {"family": "ip", "name": "reassembly_timeout", "handle": 4}}, {"chain": {"family": "ip", "table": "reassembly_timeout", "name": "before", "handle": 1, "type": "filter", "hook": "output", "prio": -301, "policy": "accept"}}, {"chain": {"family": "ip", "table": "reassembly_timeout", "name": "tracked", "handle": 2, "type": "filter", "hook": "output", "prio": -199, "policy": "accept"}}, {"chain": {"family": "ip", "table": "reassembly_timeout", "name": "output", "handle": 3, "type": "filter", "hook": "output", "prio": 0, "policy": "drop"}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "before", "handle": 4, "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"mangle": {"key": {"meta": {"key": "nftrace"}}, "value": 1}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "before", "handle": 5, "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"log": {"prefix": "TIMEOUT_OUTPUT", "group": 42, "snaplen": 65531, "queue-threshold": 1}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "tracked", "handle": 6, "comment": "TIMEOUT_RELATED", "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 4}}, {"counter": {"packets": 0, "bytes": 0}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "tracked", "handle": 7, "comment": "TIMEOUT_INVALID", "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 1}}, {"counter": {"packets": 1, "bytes": 576}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "tracked", "handle": 8, "comment": "TIMEOUT_NEW", "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 8}}, {"counter": {"packets": 0, "bytes": 0}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "tracked", "handle": 9, "comment": "TIMEOUT_ESTABLISHED", "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 2}}, {"counter": {"packets": 0, "bytes": 0}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "tracked", "handle": 10, "comment": "TIMEOUT_UNTRACKED", "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"match": {"op": "in", "left": {"ct": {"key": "state"}}, "right": 64}}, {"counter": {"packets": 0, "bytes": 0}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "tracked", "handle": 11, "expr": [{"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 1}}, {"log": {"prefix": "TIMEOUT_TRACKED", "group": 42, "snaplen": 65531, "queue-threshold": 1}}]}}, {"rule": {"family": "ip", "table": "reassembly_timeout", "chain": "output", "handle": 12, "comment": "ALLOW_REASSEMBLY_TIMEOUT", "expr": [{"match": {"op": "==", "left": {"payload": {"protocol": "icmp", "field": "type"}}, "right": 11}}, {"match": {"op": "==", "left": {"payload": {"protocol": "icmp", "field": "code"}}, "right": 1}}, {"counter": {"packets": 1, "bytes": 576}}, {"accept": null}]}}]}"#

private def object (values : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj values
private def number (value : Nat) : Lean.Json := Lean.toJson value
private def accept : Lean.Json := object [("accept", .null)]
private def count : Lean.Json := object [("counter", object [("packets", number 1), ("bytes", number 576)])]

private def predicate (field : String) (value : Lean.Json) (operator : String := "==")
    (extra : List (String × Lean.Json) := []) : Lean.Json :=
  object [("match", object [("op", .str operator), ("left", object [("payload",
    object ([("protocol", .str "icmp"), ("field", .str field)] ++ extra))]), ("right", value)])]

private def protocol (value : Nat) : Lean.Json := object [("match", object [
  ("op", .str "=="), ("left", object [("meta", object [("key", .str "l4proto")])]), ("right", number value)])]

private def state (value : Nat) : Lean.Json := object [("match", object [
  ("op", .str "in"), ("left", object [("ct", object [("key", .str "state")])]), ("right", number value)])]

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def reject (value : Except String α) (label : String) : IO Unit :=
  match value with
  | .ok _ => throw (IO.userError s!"Expected an ICMP output import error: {label}")
  | .error _ => pure ()

private def modifyObject (json : Lean.Json) (index : Nat) (kind : String) (change : Lean.Json → Lean.Json) : IO Lean.Json := do
  let objects ← unwrap ((← unwrap (json.getObjVal? "nftables")).getArr?)
  let value ← unwrap (objects[index]!.getObjVal? kind)
  pure (json.setObjVal! "nftables" (.arr (objects.set! index (object [(kind, change value)]))))

private def expressions (json : Lean.Json) (values : List Lean.Json) : IO Lean.Json :=
  modifyObject json 13 "rule" (fun rule => rule.setObjVal! "expr" (Lean.toJson values))

private def header (protocol : Packet.Protocol := Packet.Protocol.icmp) : Header :=
  ⟨3405803778, 3221225986, protocol, 0, 0⟩

example (snapshot : Snapshot) (fallback : Action) (kind : Protocol.ICMP.Kind)
    (state : StatefulACL.CTState) (header : Header) :
    StatefulACL.Policy.evaluate fallback (snapshot.compile kind) state header = snapshot.evaluate kind state header :=
  snapshot.compile_evaluate _ _ _ _

private def positiveTests (json : Lean.Json) : IO Unit := do
  let snapshot ← unwrap (Snapshot.fromJson json)
  ensure (snapshot.table == "reassembly_timeout" && snapshot.chain == "output" && snapshot.hook == "output" &&
      snapshot.priority == 0 && snapshot.policyDefault == .deny && snapshot.chainIndex == 4 &&
      snapshot.tableIndex == 1 && snapshot.rules.length == 1 &&
      snapshot.policySourceID == "nftables[4].chain.policy")
    "The full native table must select the exact output filter and preserve its original location."
  let some rule := snapshot.rules.head? | throw (IO.userError "Expected the native timeout rule.")
  ensure (rule.typeTests == [11] && rule.codeTests == [1] && rule.typeExpressionIndices == [0] &&
      rule.codeExpressionIndices == [1] && rule.counterExpressionIndices == [2] &&
      rule.base.objectIndex == 13 && rule.base.verdictIndex == 3 && rule.base.expressionIndices == [0, 1, 2, 3] &&
      rule.base.sourceID == "nftables[13].rule.handle[12]" && rule.base.protocol == some Packet.Protocol.icmp &&
      rule.base.comment == some "ALLOW_REASSEMBLY_TIMEOUT")
    "ICMP guards, the implied protocol, counter indices, and rule provenance must survive import."
  for kind in [Protocol.ICMP.Kind.timeExceeded, .reassemblyTimeout, .fragmentationNeeded 600] do
    for ct in [StatefulACL.CTState.new, .established, .related, .invalid, .untracked] do
      for protocol in [Packet.Protocol.icmp, .udp, .tcp] do
        let expected : Action := if kind == .reassemblyTimeout && protocol == Packet.Protocol.icmp then .permit else .deny
        ensure (snapshot.evaluate kind ct (header protocol) == expected &&
            StatefulACL.Policy.evaluate .permit (snapshot.compile kind) ct (header protocol) == expected)
          "The native timeout rule must reject other ICMP kinds and non-ICMP headers under every supplied CT state."
  let time ← unwrap (Snapshot.fromJson (← expressions json [predicate "type" (number 11), predicate "code" (number 0), accept]))
  ensure (time.evaluate .timeExceeded .invalid header == .permit && time.evaluate .reassemblyTimeout .invalid header == .deny)
    "Code zero and code one must remain distinct after compilation."
  let frag ← unwrap (Snapshot.fromJson (← expressions json [predicate "type" (number 3), predicate "code" (number 4), accept]))
  ensure (frag.evaluate (.fragmentationNeeded 1280) .invalid header == .permit &&
      frag.evaluate .reassemblyTimeout .invalid header == .deny)
    "Type three/code four must not become a generic ICMP allowance."
  let selected ← unwrap (Snapshot.fromJson (← expressions json [predicate "type" (number 11),
    state 1, predicate "code" (number 1), count, accept]))
  let some rule := selected.rules.head? | throw (IO.userError "Expected a guarded state rule.")
  ensure (rule.base.stateExpressionIndex == some 1 && rule.base.verdictIndex == 4 &&
      rule.counterExpressionIndices == [3] && selected.evaluate .reassemblyTimeout .invalid header == .permit &&
      selected.evaluate .reassemblyTimeout .related header == .deny)
    "Base CT-state conditions must retain native expression indices and combine with type/code guards."
  let observer ← modifyObject json 8 "rule" (fun rule => rule.setObjVal! "expr" (Lean.toJson [object [("drop", .null)]]))
  let unchanged ← unwrap (Snapshot.fromJson observer)
  ensure (unchanged.evaluate .reassemblyTimeout .invalid header == snapshot.evaluate .reassemblyTimeout .invalid header)
    "Other declared chains remain outside this selected-chain compiler's claim."

private def negativeTests (json : Lean.Json) : IO Unit := do
  let good := [predicate "type" (number 11), predicate "code" (number 1)]
  for invalid in [
      [predicate "type" (number 256), accept],
      [predicate "code" (number 256), accept],
      [predicate "type" (Lean.toJson (-1 : Int)), accept],
      [predicate "code" (.str "reassembly-timeout"), accept],
      [predicate "checksum" (number 1), accept],
      [predicate "type" (number 11) "!=", accept],
      [predicate "type" (Lean.toJson ([11] : List Nat)) "in", accept],
      [predicate "type" (number 11) "==" [("len", number 8)], accept],
      [predicate "code" (number 1) "==" [("offset", number 0)], accept],
      [predicate "type" (number 11), predicate "type" (number 11), accept],
      [predicate "code" (number 1), predicate "code" (number 0), accept],
      good ++ [protocol 17, accept],
      good ++ [object [("counter", .null)], accept],
      good ++ [count, count, accept],
      good ++ [object [("counter", object [("packets", Lean.toJson (-1 : Int)), ("bytes", number 576)])], accept],
      good ++ [object [("counter", object [("packets", number 1), ("bytes", number 18446744073709551616)])], accept],
      good ++ [object [("counter", object [("packets", number 1), ("bytes", number 576), ("name", .str "counter")])], accept],
      good ++ [object [("log", object [])], accept],
      good ++ [object [("accept", number 1)]],
      good ++ [accept, predicate "code" (number 1)],
      good ++ [count],
      good ++ [state 1, state 1, accept]] do
    reject (Snapshot.fromJson (← expressions json invalid)) "unsupported or contradictory rule expression"
  for (field, value) in [("hook", Lean.Json.str "forward"), ("type", .str "nat"), ("prio", Lean.toJson (1 : Int)),
      ("policy", .str "continue"), ("family", .str "ip6"), ("name", .str "renamed")] do
    reject (Snapshot.fromJson (← modifyObject json 4 "chain" (fun chain => chain.setObjVal! field value)))
      "wrong named output filter"
  reject (Snapshot.fromJson (← modifyObject json 13 "rule" (fun rule => rule.setObjVal! "chain" (.str "missing"))))
    "undeclared chain"
  reject (Snapshot.fromJson (← modifyObject json 13 "rule" (fun rule => rule.setObjVal! "table" (.str "wrong"))))
    "wrong rule table"
  let objects ← unwrap ((← unwrap (json.getObjVal? "nftables")).getArr?)
  reject (Snapshot.fromJson (json.setObjVal! "nftables" (.arr (objects.push objects[13]!)))) "duplicate selected rule handle"
  reject (Snapshot.fromJson (json.setObjVal! "nftables" (.arr (objects.push objects[4]!)))) "duplicate output chain"
  let moved ← modifyObject json 13 "rule" (fun rule => rule.setObjVal! "chain" (.str "tracked"))
  let empty ← unwrap (Snapshot.fromJson moved)
  ensure (empty.rules.isEmpty && empty.evaluate .reassemblyTimeout .invalid header == .deny)
    "Moving a rule outside the selected chain must not leave a fabricated selected-chain allowance."

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse nativeJSON)
  positiveTests json
  negativeTests json
  IO.println "Native ICMP output policy import tests passed."

end NetlibTest.NftablesICMPControl
