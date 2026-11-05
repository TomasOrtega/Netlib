import Netlib.Import.NftablesPredefrag

namespace NetlibTest.NftablesPredefrag

open Netlib Packet Protocol
open Import.NftablesPredefrag

private def ns : IngressAttachment.NamespaceRef := ⟨20, 1⟩
private def port (index : Nat) (bounded : 0 < index ∧ index ≤ 2147483647) (birth : Nat := 1) : IngressAttachment.InterfaceRef :=
  ⟨ns, ⟨index, bounded⟩, birth⟩
private def bindings : List Binding := [⟨"client", port 2 (by decide)⟩]
private def header : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩

private def sample : String := r#"{"nftables":[
{"metainfo":{"version":"1.1.3","release_name":"Commodore Bullmoose #4","json_schema_version":1}},
{"table":{"family":"ip","name":"fragment_test","handle":1}},
{"chain":{"family":"ip","table":"fragment_test","name":"early","handle":1,"type":"filter","hook":"prerouting","prio":-450,"policy":"drop"}},
{"rule":{"family":"ip","table":"fragment_test","chain":"early","handle":2,"comment":"client","expr":[
{"match":{"op":"==","left":{"meta":{"key":"iif"}},"right":"client"}},
{"match":{"op":"==","left":{"payload":{"protocol":"ip","field":"saddr"}},"right":"192.0.2.2"}},
{"match":{"op":"==","left":{"payload":{"protocol":"ip","field":"daddr"}},"right":"203.0.113.2"}},
{"match":{"op":"==","left":{"payload":{"protocol":"ip","field":"protocol"}},"right":17}},
{"log":{"prefix":"FRAG_ALLOW","group":42,"snaplen":65531,"queue-threshold":1}},
{"accept":null}]}},
{"rule":{"family":"ip","table":"fragment_test","chain":"early","handle":3,"expr":[
{"log":{"prefix":"FRAG_DROP","group":42,"snaplen":65531,"queue-threshold":1}},
{"drop":null}]}}]}"#

private def parse (text : String) (selected : List Binding := bindings) : Except String Snapshot := do
  Snapshot.fromJson ns selected (← Import.Json.parse text)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)
private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

example (snapshot : Snapshot) (index : Nat) (first second : Header)
    (same : Packet.IPv4Envelope.ofHeader first = Packet.IPv4Envelope.ofHeader second) :
    snapshot.guard.policy.allows index first = snapshot.guard.policy.allows index second :=
  IngressPolicy.noPorts_port_independent snapshot.guard.policy snapshot.noPorts index first second same

def run : IO Unit := do
  let named ← load (parse sample)
  let numeric ← load (parse (sample.replace "\"right\":\"client\"" "\"right\":2"))
  ensure (named.source.source.priority == -450 && named.source.source.hook == "prerouting" &&
    named.source.ns == ns && named.source.bindings == bindings && named.source.raw == (← load (Import.Json.parse sample)) &&
    IngressPolicy.noPorts named.guard.policy)
    "Import must retain the actual early priority, namespace, bindings, source JSON, and absence of transport reads."
  let some first := named.source.rules[0]? | throw (IO.userError "Missing selected early source rule.")
  let some fallback := named.source.rules[1]? | throw (IO.userError "Missing selected fallback source rule.")
  ensure (first.objectIndex == 3 && first.handle == 2 && first.ingressExpressionIndex == some 0 &&
    first.expressionIndices == [0, 1, 2, 3, 4, 5] && first.logExpressionIndex == some 4 && first.verdictIndex == 5 &&
    fallback.objectIndex == 4 && fallback.handle == 3 && fallback.logExpressionIndex == some 0 && fallback.verdictIndex == 1)
    "Rule provenance must retain actual object, ingress, log, verdict, and expression positions."
  for index in [0, 1, 2, 3, 2147483647, 1099511627776] do
    for selected in [header, { header with sourcePort := 0, destinationPort := 65535 },
        { header with source := 3221225987 }, { header with destination := 3405803777 },
        { header with protocol := Packet.Protocol.tcp }] do
      let wanted := index == 2 && selected.source == header.source && selected.destination == header.destination &&
        selected.protocol == Packet.Protocol.udp
      ensure (named.guard.policy.allows index selected == wanted && named.source.permits index selected == wanted &&
        numeric.guard.policy.allows index selected == wanted)
        "Named numeric-iif exports must preserve all-index IPv4 selection independently of transport ports."
  let reused ← load (parse sample [⟨"client", port 2 (by decide) 2⟩])
  ensure (reused.guard.policy.allows 2 header)
    "Actual numeric rules do not gain lifetime awareness when an interface index is reused."
  let transport := r#"{"match":{"op":"==","left":{"payload":{"protocol":"udp","field":"dport"}},"right":{"range":[0,65535]}}},"#
  let predicate := r#"{"match":{"op":"==","left":{"payload":{"protocol":"ip","field":"protocol"}},"right":17}},"#
  for selector in [transport, transport.replace "\"udp\"" "\"tcp\"",
      transport.replace "{\"range\":[0,65535]}" "8080",
      transport.replace "\"dport\"" "\"sport\""] do
    reject (parse (sample.replace predicate selector))
      "Every transport read must reject, including a tautological full-port range."
  for text in [sample.replace "-450" "-400", sample.replace "-450" "-300", sample.replace "-450" "-451",
      sample.replace "\"prerouting\"" "\"forward\"", sample.replace "\"prerouting\"" "\"input\"",
      sample.replace "\"iif\"" "\"iifname\"", sample.replace "\"right\":\"client\"" "\"right\":0",
      sample.replace "\"right\":\"client\"" "\"right\":2147483648",
      sample.replace "\"right\":\"client\"" "\"right\":\"unknown\"",
      sample.replace "\"op\":\"==\"" "\"op\":\"!=\"",
      sample.replace "FRAG_ALLOW" "FRAG_DROP", sample.replace "FRAG_ALLOW" "ATTACH_ALLOW",
      sample.replace "\"group\":42" "\"group\":41", sample.replace "\"snaplen\":65531" "\"snaplen\":64",
      sample.replace "\"queue-threshold\":1" "\"queue-threshold\":2",
      sample.replace "{\"accept\":null}" "{\"accept\":null},{\"drop\":null}",
      sample.replace "{\"accept\":null}" ((predicate.dropEnd 1).toString ++ ",{\"accept\":null}"),
      sample.replace "{\"accept\":null}" "{\"accept\":null,\"logExpressionIndex\":4}"] do
    reject (parse text) "Unsupported early hooks, selectors, logging, order, or verdict envelopes must reject."
  let iif := r#"{"match":{"op":"==","left":{"meta":{"key":"iif"}},"right":"client"}},"#
  reject (parse (sample.replace iif (iif ++ iif))) "A source rule cannot claim two input-interface predicates."
  reject (parse (sample.replace predicate (predicate ++ predicate))) "Repeated IPv4 predicates must not overwrite earlier source selectors."
  reject (parse sample (bindings ++ [⟨"client", port 3 (by decide)⟩]))
    "Ambiguous exported names cannot resolve through first occurrence."
  reject (parse sample (bindings ++ [⟨"other", port 2 (by decide)⟩]))
    "A numeric index must resolve to one supplied live interface reference."
  reject (parse sample [⟨"client", { port 2 (by decide) with ns := ⟨30, 1⟩ }⟩])
    "Name resolution cannot import a binding from another namespace lifetime."

end NetlibTest.NftablesPredefrag
