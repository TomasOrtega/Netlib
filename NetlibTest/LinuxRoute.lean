import Netlib.Import.LinuxRoute

namespace NetlibTest.LinuxRoute

open Netlib Netlib.Packet Netlib.Import.LinuxRoute

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"Expected a route input error: {label}")
  | .error _ => pure ()

private def bindings : List Binding :=
  [⟨"eth0", "upstream", some 3221225985⟩, ⟨"eth0", "lan", none⟩, ⟨"eth1", "service", none⟩]

private def nativeFormat : String := r#"[
  {"dst":"default","gateway":"192.0.2.1","dev":"eth0","protocol":"static","metric":100,"flags":[]},
  {"dst":"192.0.2.0/24","dev":"eth0","protocol":"kernel","scope":"link","prefsrc":"192.0.2.2","flags":[]},
  {"dst":"198.51.100.0/24","dev":"eth1","protocol":"static","scope":"link","metric":500,"flags":[]},
  {"type":"blackhole","dst":"198.51.100.128/25","protocol":"static","metric":9999,"flags":[]},
  {"type":"unreachable","dst":"203.0.113.7","flags":[]},
  {"type":"prohibit","dst":"203.0.113.8","flags":[]}
]"#

private def normal : String :=
  r#"[{"dst":"default","gateway":"192.0.2.1","dev":"eth0","flags":[]}]"#

/-- Captured with iproute2 6.19.0 in a disposable Linux network namespace. -/
private def captured : String := r#"[{"dst":"default","gateway":"172.17.0.1","dev":"eth0","flags":[]},{"dst":"172.17.0.0/16","dev":"eth0","protocol":"kernel","scope":"link","prefsrc":"172.17.0.2","flags":[]},{"dst":"198.51.100.0/24","dev":"eth0","scope":"link","metric":500,"flags":[]},{"type":"blackhole","dst":"198.51.100.128/25","metric":9999,"flags":[]},{"type":"unreachable","dst":"203.0.113.7","flags":[]},{"type":"prohibit","dst":"203.0.113.8","flags":[]}]"#

private def capturedTests : IO Unit := do
  let snapshot ← unwrap (Snapshot.parse captured
    [⟨"eth0", "upstream", some 2886795265⟩, ⟨"eth0", "segment", none⟩])
  ensure (snapshot.routes.length == 6) "The actual iproute2 export lost records."
  for (destination, expected) in [
      ("8.8.8.8", some "upstream"), ("172.17.0.8", some "segment"),
      ("198.51.100.1", some "segment"), ("198.51.100.200", none),
      ("203.0.113.7", none), ("203.0.113.8", none)] do
    let address ← unwrap (Netlib.Import.IPv4.parseAddress destination)
    ensure (Routing.nextHop snapshot.compile address == expected)
      s!"The actual export has an incorrect compiled result for {destination}."

example (snapshot : Snapshot) (address : Address) :
    Routing.nextHop snapshot.compile address = snapshot.nextNode address :=
  snapshot.nextHop_correct address

private def forwardingTests : IO Unit := do
  let snapshot ← unwrap (Snapshot.parse nativeFormat bindings)
  ensure (snapshot.routes.length == 6) "The route snapshot lost records."
  ensure (snapshot.routes.map Route.index == [0, 1, 2, 3, 4, 5])
    "The route snapshot lost original JSON indices."
  ensure (snapshot.routes.map Route.location == ["/0", "/1", "/2", "/3", "/4", "/5"])
    "The route snapshot changed source locations."
  let first ← match snapshot.routes.head? with
    | some first => pure first
    | none => throw (IO.userError "The route snapshot is empty.")
  ensure (first.metric == some 100 && first.protocol == some "static")
    "The route snapshot lost its metric or protocol metadata."
  ensure ((first.original.getObjVal? "gateway" >>= Lean.Json.getStr?).toOption == some "192.0.2.1")
    "The route snapshot changed the original gateway evidence."
  let connected ← match snapshot.routes[1]? with
    | some connected => pure connected
    | none => throw (IO.userError "The connected route is missing.")
  ensure (connected.scope == some "link" && connected.preferredSource == some 3221225986)
    "The connected route lost scope or preferred-source metadata."
  for (destination, expected) in [
      ("8.8.8.8", some "upstream"), ("192.0.2.5", some "lan"),
      ("198.51.100.3", some "service"), ("198.51.100.128", none),
      ("198.51.100.255", none), ("203.0.113.7", none), ("203.0.113.8", none)] do
    let address ← unwrap (Netlib.Import.IPv4.parseAddress destination)
    ensure (Routing.nextHop snapshot.compile address == expected)
      s!"Incorrect compiled forwarding result for {destination}."
    ensure (snapshot.nextNode address == expected)
      s!"Incorrect structured route meaning for {destination}."
  let empty ← unwrap (Snapshot.parse "[]" bindings)
  ensure ((Routing.nextHop empty.compile 0).isNone) "An empty table supplied a route."
  for table in [r#""main""#, r#""254""#, "254"] do
    let text := normal.replace "\"flags\":[]" s!"\"table\":{table}"
    let _ ← unwrap (Snapshot.parse text bindings)

private def validationTests : IO Unit := do
  for (label, invalid) in [
      ("object instead of array", "{}"), ("null root", "null"), ("non-object entry", "[null]"),
      ("missing destination", "[{\"dev\":\"eth0\"}]"),
      ("missing output device", "[{\"dst\":\"default\"}]"),
      ("unknown device", normal.replace "eth0" "eth9"),
      ("gateway binding mismatch", normal.replace "192.0.2.1" "192.0.2.9"),
      ("noncanonical destination", normal.replace "default" "192.0.2.1/24"),
      ("noncanonical default", normal.replace "default" "192.0.2.1/0"),
      ("IPv6 destination", normal.replace "default" "2001:db8::/32"),
      ("IPv6 gateway", normal.replace "192.0.2.1" "2001:db8::1"),
      ("leading zero in address", normal.replace "192.0.2.1" "192.0.02.1"),
      ("oversized prefix", normal.replace "default" "192.0.2.0/33"),
      ("non-main table", normal.replace "\"flags\":[]" "\"table\":100"),
      ("local table", normal.replace "\"flags\":[]" "\"table\":\"local\""),
      ("host scope", normal.replace "\"flags\":[]" "\"scope\":\"host\""),
      ("non-string scope", normal.replace "\"flags\":[]" "\"scope\":253"),
      ("non-string protocol", normal.replace "\"flags\":[]" "\"protocol\":2"),
      ("empty protocol", normal.replace "\"flags\":[]" "\"protocol\":\"\""),
      ("negative metric", normal.replace "\"flags\":[]" "\"metric\":-1"),
      ("fractional metric", normal.replace "\"flags\":[]" "\"metric\":1.5"),
      ("oversized metric", normal.replace "\"flags\":[]" "\"metric\":4294967296"),
      ("unsupported flag", normal.replace "[]" "[\"linkdown\"]"),
      ("invalid flag type", normal.replace "\"flags\":[]" "\"flags\":null"),
      ("duplicate JSON key", normal.replace "\"dst\":\"default\"" "\"dst\":\"default\",\"dst\":\"192.0.2.0/24\"") ] do
    reject (Snapshot.parse invalid bindings) label
  for field in ["multipath", "nexthops", "nhid", "encap", "via", "from", "src", "tos", "pref", "mtu", "expires", "cache"] do
    let invalid := normal.replace "\"flags\":[]" s!"\"{field}\":0"
    reject (Snapshot.parse invalid bindings) s!"unsupported {field}"
  for kind in ["local", "broadcast", "throw", "multicast", "nat", "anycast"] do
    let invalid := normal.replace "\"flags\":[]" s!"\"type\":\"{kind}\""
    reject (Snapshot.parse invalid bindings) s!"unsupported route type {kind}"
  for kind in ["blackhole", "unreachable", "prohibit"] do
    let invalid := normal.replace "\"flags\":[]" s!"\"type\":\"{kind}\""
    reject (Snapshot.parse invalid bindings) "A drop route has forwarding fields."
  reject (Snapshot.parse normal (bindings ++ bindings)) "Duplicate device and gateway bindings."
  reject (Snapshot.parse normal [⟨"eth0", "other", none⟩]) "A gateway does not match a direct binding."
  reject (Snapshot.parse normal [⟨"", "upstream", some 3221225985⟩]) "An empty interface binding."
  reject (Snapshot.parse normal [⟨"eth0", "", some 3221225985⟩]) "An empty next-node binding."

private def ambiguityTests : IO Unit := do
  for text in [
      r#"[{"dst":"192.0.2.0/24","dev":"eth0"},{"dst":"192.0.2.0/24","dev":"eth1"}]"#,
      r#"[{"dst":"192.0.2.0/24","dev":"eth0","metric":10},{"dst":"192.0.2.0/24","dev":"eth1","metric":20}]"#,
      r#"[{"dst":"192.0.2.1","dev":"eth0"},{"dst":"192.0.2.1/32","dev":"eth1"}]"#,
      r#"[{"dst":"default","dev":"eth0"},{"dst":"0.0.0.0/0","dev":"eth1"}]"# ] do
    reject (Snapshot.parse text bindings) "An ambiguous equal-prefix route pair."
  match Snapshot.parse r#"[{"dst":"default","dev":"eth0"},{"dst":"192.0.2.0/24","dev":"unknown"}]"# bindings with
  | .ok _ => throw (IO.userError "The second route has an unknown output interface.")
  | .error message =>
    ensure ((message.splitOn "route /1:").length > 1) "The input error lost its JSON index."

def run : IO Unit := do
  capturedTests
  forwardingTests
  validationTests
  ambiguityTests
  IO.println "Linux route snapshot tests passed."

end NetlibTest.LinuxRoute
