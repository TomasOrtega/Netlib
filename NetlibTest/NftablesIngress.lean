import Netlib.Import.NftablesIngress

namespace NetlibTest.NftablesIngress

open Netlib Packet Protocol
open Import.NftablesIngress

private def ns : IngressAttachment.NamespaceRef := ⟨1, 0⟩
private def interface (index : Nat) (positive : 0 < index) (bounded : index ≤ 2147483647)
    (birth : Nat := 0) : IngressAttachment.InterfaceRef := ⟨ns, ⟨index, positive, bounded⟩, birth⟩
private def links : List Binding := [⟨"legitr", interface 2 (by decide) (by decide)⟩]
private def header : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩

private def sample : String := r#"{"nftables":[
{"metainfo":{"version":"1.1.3","release_name":"Commodore Bullmoose #4","json_schema_version":1}},
{"table":{"family":"ip","name":"attachment_proto","handle":1}},
{"chain":{"family":"ip","table":"attachment_proto","name":"guard","handle":1,"type":"filter","hook":"prerouting","prio":-300,"policy":"drop"}},
{"rule":{"family":"ip","table":"attachment_proto","chain":"guard","handle":2,"expr":[{"match":{"op":"==","left":{"meta":{"key":"iif"}},"right":"legitr"}},{"accept":null}]}}]}"#

private def parse (text : String) (bindings : List Binding := links) : Except String Snapshot := do
  Snapshot.fromJson ns bindings (← Import.Json.parse text)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def run : IO Unit := do
  let named ← load (parse sample)
  let numeric ← load (parse (sample.replace "\"right\":\"legitr\"" "\"right\":2"))
  for index in [0, 1, 2, 3, 2147483647] do
    ensure (named.permits index header == (index == 2) && numeric.permits index header == named.permits index header)
      "A named numeric-iif export must preserve its exact kernel-index decision."
    have _ := named.compile_allows index header
  let reused ← load (parse sample [⟨"legitr", interface 2 (by decide) (by decide) 1⟩])
  ensure (reused.permits 2 header)
    "An actual numeric rule still permits a reused index; lifetime labels cannot silently repair it."
  let renamed ← load (parse (sample.replace "\"legitr\"" "\"renamed\"")
    [⟨"renamed", interface 2 (by decide) (by decide)⟩])
  ensure (renamed.permits 2 header)
    "A renamed export must resolve the unchanged numeric index through its current binding."
  for changed in [sample.replace "\"iif\"" "\"iifname\"",
      sample.replace "\"legitr\"" "\"unknown\"",
      sample.replace "\"prerouting\"" "\"forward\"",
      sample.replace "-300" "-199", sample.replace "\"right\":\"legitr\"" "\"right\":0",
      sample.replace "\"right\":\"legitr\"" "\"right\":2147483648"] do
    reject (parse changed) "Unsupported ingress syntax or kernel-index bounds must fail."
  let logged := sample.replace "{\"accept\":null}"
    "{\"log\":{\"prefix\":\"ATTACH_ALLOW\",\"group\":42,\"snaplen\":65531,\"queue-threshold\":1}},{\"accept\":null}"
  let observed ← load (parse logged)
  ensure (observed.permits 2 header && observed.rules.head?.any (fun rule => rule.logExpressionIndex == some 1))
    "The selected NFLOG expression must retain its source index without changing the verdict."
  reject (parse (logged.replace "ATTACH_ALLOW" "ATTACH_DROP")) "A decision label must agree with its actual verdict."
  reject (parse sample (links ++ [⟨"legitr", interface 3 (by decide) (by decide)⟩]))
    "Ambiguous current interface names cannot be resolved by first occurrence."
  reject (parse sample (links ++ [⟨"other", interface 2 (by decide) (by decide)⟩]))
    "A numeric index must identify one current interface lifetime."

end NetlibTest.NftablesIngress
