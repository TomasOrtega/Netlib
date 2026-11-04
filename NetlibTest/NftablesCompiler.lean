import Netlib.Compile.Nftables

namespace NetlibTest.NftablesCompiler

open Netlib.Packet

private def web : Match := {
  source := some ⟨167772161, 24⟩
  destination := some ⟨3325256711, 24⟩
  protocol := some Protocol.tcp
  sourcePorts := some ⟨1024, 65535⟩
  destinationPorts := some ⟨443, 444⟩ }

private def dns : Match :=
  { protocol := some Protocol.udp, destinationPorts := some (PortRange.single 53) }

private def policy : List Netlib.Compile.ACL.Intent := [
  ⟨"WEB", web, .permit⟩,
  ⟨"DNS", dns, .permit⟩,
  ⟨"EXPERIMENTAL", { protocol := some 253 }, .permit⟩,
  ⟨"SSH-DENIED", { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 22) }, .deny⟩]

example (emitted : Netlib.Compile.Nftables.Emitted policy) (header : Header) :
    emitted.snapshot.permits header = true ↔ Netlib.Compile.ACL.Meaning policy header :=
  emitted.correct header

example (emitted : Netlib.Compile.Nftables.Emitted policy) (header : Header) :
    emitted.snapshot.compile.allows header = emitted.compiled.rules.allows header :=
  emitted.compiled_eq header

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap {intents : List Netlib.Compile.ACL.Intent}
    (result : Except (Netlib.Compile.Nftables.Error intents) (Netlib.Compile.Nftables.Emitted intents)) :
    IO (Netlib.Compile.Nftables.Emitted intents) :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def parse (text : String) : IO Netlib.Import.Nftables.Snapshot :=
  match Netlib.Import.Nftables.Snapshot.parse text with
  | .ok snapshot => pure snapshot
  | .error error => throw (IO.userError error)

private def checkRoundtrip (emitted : Netlib.Compile.Nftables.Emitted intents) : IO Unit := do
  let parsed ← parse emitted.toJson.pretty
  ensure (parsed.table == "netlib" && parsed.chain == "forward" && parsed.priority == 0 && parsed.policy == .deny)
    "The emitted base-chain contract changed."
  ensure (parsed.rules.map (·.comment) == emitted.compiled.ruleIds.map some)
    "Rule comments lost their requirement IDs."
  let partition := Partition.ofRulesAndRoutes [parsed.compile, emitted.compiled.rules]
    ([] : List (List (Netlib.Routing.Entry Unit)))
  for header in partition.representatives do
    ensure (parsed.permits header == emitted.snapshot.permits header)
      "A parser roundtrip changed a packet decision."
  ensure (Partition.checkACLRefines parsed.compile emitted.compiled.rules &&
    Partition.checkACLRefines emitted.compiled.rules parsed.compile)
    "The parser roundtrip changed the complete header-space meaning."

private def policyTests : IO Unit := do
  let emitted ← unwrap (Netlib.Compile.Nftables.compile policy)
  ensure (emitted.requirementIds == ["WEB", "DNS", "EXPERIMENTAL", "SSH-DENIED"])
    "The native policy lost an intent requirement ID."
  ensure (emitted.snapshot.rules.map (·.sourceID) == ["WEB", "DNS", "EXPERIMENTAL"])
    "The structured source rules lost their requirement IDs."
  ensure (emitted.snapshot.rules.map (·.handle) == [3, 4, 5]) "The emitted rule handles overlap."
  checkRoundtrip emitted
  let parsed ← parse emitted.toJson.pretty
  for header in ([⟨167772161, 3325256705, Protocol.tcp, 50000, 443⟩,
      ⟨0, 0, Protocol.udp, 0, 53⟩, ⟨4294967295, 4294967295, 253, 65535, 65535⟩] : List Header) do
    ensure (parsed.permits header) "The native policy denied a permitted packet."
  for header in ([⟨167772161, 3325256705, Protocol.tcp, 50000, 22⟩,
      ⟨167772161, 3325256705, Protocol.tcp, 1023, 443⟩,
      ⟨167772416, 3325256705, Protocol.tcp, 50000, 443⟩,
      ⟨0, 0, Protocol.tcp, 0, 53⟩] : List Header) do
    ensure (!parsed.permits header) "The native policy admitted a denied or unspecified packet."
  let forbiddenOnly : List Netlib.Compile.ACL.Intent := [⟨"DENIED", {}, .deny⟩]
  let empty ← unwrap (Netlib.Compile.Nftables.compile forbiddenOnly)
  ensure (empty.snapshot.rules.isEmpty && empty.requirementIds == ["DENIED"])
    "The forbidden-only policy lost its default or requirement IDs."
  checkRoundtrip empty
  for block in ([⟨123, 0⟩, ⟨4294967295, 32⟩] : List Prefix) do
    let prefixPolicy : List Netlib.Compile.ACL.Intent := [⟨"PREFIX", { source := some block }, .permit⟩]
    let emitted ← unwrap (Netlib.Compile.Nftables.compile prefixPolicy)
    checkRoundtrip emitted

private def unsupportedTests : IO Unit := do
  for test in ([
      { destinationPorts := some (PortRange.single 443) },
      { protocol := some Protocol.icmp, sourcePorts := some (PortRange.single 0) },
      { protocol := some Protocol.tcp, destinationPorts := some ⟨20, 10⟩ }] : List Match) do
    let intents : List Netlib.Compile.ACL.Intent := [⟨"UNREPRESENTABLE", test, .permit⟩]
    match Netlib.Compile.Nftables.compile intents with
    | .error (.unsupported id) => ensure (id == "UNREPRESENTABLE") "The capability error lost its requirement ID."
    | .error error => throw (IO.userError s!"Expected a capability error: {error.describe}")
    | .ok _ => throw (IO.userError "An unsupported packet predicate was silently changed.")
  let intents : List Netlib.Compile.ACL.Intent := [⟨"VALID", dns, .permit⟩]
  match Netlib.Compile.Nftables.compile intents 0 with
  | .error (.intent (.exhausted _ 0)) => pure ()
  | _ => throw (IO.userError "The native compiler lost the source compiler's budget error.")
  let longId := String.ofList (List.replicate 129 'A')
  match Netlib.Compile.Nftables.compile [⟨longId, dns, .permit⟩] with
  | .error (.longId actual) => ensure (actual == longId) "An oversized comment ID was truncated."
  | _ => throw (IO.userError "An oversized native comment was emitted.")
  let limitId := String.ofList (List.replicate 128 'A')
  let atLimit ← unwrap (Netlib.Compile.Nftables.compile [⟨limitId, dns, .permit⟩])
  checkRoundtrip atLimit

private def permitOnly (id : String) : Netlib.Compile.ACL.Certified [⟨id, {}, .permit⟩] where
  entries := Netlib.Compile.ACL.emit [⟨id, {}, .permit⟩]
  generated := rfl
  consistent := by
    intro header conflict
    simpa [Netlib.Compile.ACL.Forbidden] using conflict.2

private def escapedIdTest : IO Unit := do
  let id := "quoted\" slash\\ newline\n"
  let emitted : Netlib.Compile.Nftables.Emitted [⟨id, {}, .permit⟩] := {
    compiled := permitOnly id
    supported := by
      intro intent member
      have same := List.mem_singleton.mp member
      subst intent
      rfl
    comments := by
      intro intent member
      have same := List.mem_singleton.mp member
      subst intent
      decide }
  checkRoundtrip emitted
  let parsed ← parse emitted.toJson.pretty
  ensure (parsed.rules.map (·.comment) == [some id]) "JSON escaping changed a comment's bytes."

private def nativeRoundtripTest : IO Unit := do
  let original ← parse (← IO.FS.readFile "examples/linux/captured-compiler-input.json")
  let loaded ← parse (← IO.FS.readFile "examples/linux/captured-compiler-output.json")
  ensure (original.rules.map (·.comment) == [some "WEB", some "DNS", some "ICMP"])
    "The generated native fixture has unexpected requirement IDs."
  ensure (loaded.rules.map (·.comment) == original.rules.map (·.comment))
    "Native loading changed requirement IDs or rule order."
  let partition := Partition.ofRulesAndRoutes [original.compile, loaded.compile]
    ([] : List (List (Netlib.Routing.Entry Unit)))
  for header in partition.representatives do
    ensure (original.permits header == loaded.permits header)
      "Native re-export changed a representative packet decision."
  ensure (Partition.checkACLRefines original.compile loaded.compile &&
    Partition.checkACLRefines loaded.compile original.compile)
    "Native re-export changed the complete header-space meaning."

def run : IO Unit := do
  policyTests
  unsupportedTests
  escapedIdTest
  nativeRoundtripTest
  IO.println "Nftables compiler tests passed."

end NetlibTest.NftablesCompiler
