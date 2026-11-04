import Netlib.Compile.ACL

namespace NetlibTest.ACLCompiler

open Netlib.Packet Netlib.Compile.ACL

private def https : Match :=
  { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 443) }

private def ssh : Match :=
  { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 22) }

private def dns : Match :=
  { protocol := some Protocol.udp, destinationPorts := some (PortRange.single 53) }

private def allowHttps : Intent := ⟨"ALLOW-HTTPS", https, .permit⟩

private def denySsh : Intent := ⟨"DENY-SSH", ssh, .deny⟩

private def policy : List Intent :=
  [allowHttps, denySsh, ⟨"ALLOW-DNS", dns, .permit⟩,
    ⟨"ALLOW-APP-HTTPS", { https with source := some ⟨167772160, 8⟩ }, .permit⟩]

private def webPacket : Header := ⟨167772161, 167772162, Protocol.tcp, 50000, 443⟩

private def sshPacket : Header := { webPacket with destinationPort := 22 }

example (compiled : Certified policy) : compiled.rules.allows webPacket = true :=
  compiled.satisfies.1 webPacket ⟨allowHttps, by simp [policy], rfl, by decide⟩

example (compiled : Certified policy) : compiled.rules.allows sshPacket = false :=
  compiled.satisfies.2 sshPacket ⟨denySsh, by simp [policy], rfl, by decide⟩

example (compiled : Certified policy) (header : Header) :
    compiled.rules.allows header = true ↔ Meaning policy header := compiled.correct header

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap {intents : List Intent} (result : Except (Error intents) (Certified intents)) :
    IO (Certified intents) :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def expectInvalid (intents : List Intent) (expected : InputError) : IO Unit :=
  match compile intents with
  | .error (.invalid actual) => ensure (actual == expected) "The compiler returned the wrong input error."
  | .error error => throw (IO.userError s!"Expected an input error: {error.describe}")
  | .ok _ => throw (IO.userError "Malformed intent requirements compiled.")

private def policyTests : IO Unit := do
  let compiled ← unwrap (compile policy)
  ensure (compiled.requirementIds == ["ALLOW-HTTPS", "DENY-SSH", "ALLOW-DNS", "ALLOW-APP-HTTPS"])
    "Compilation lost an original requirement ID."
  ensure (compiled.ruleIds == ["ALLOW-HTTPS", "ALLOW-DNS", "ALLOW-APP-HTTPS"])
    "Emission changed permit provenance or input order."
  ensure (compiled.rules.all (fun rule => rule.action == .permit)) "An unexpected deny rule was emitted."
  for header in [webPacket, ⟨0, 0, Protocol.udp, 0, 53⟩,
      ⟨4294967295, 4294967295, Protocol.tcp, 65535, 443⟩] do
    ensure (compiled.rules.allows header) "A declared permitted packet was blocked."
  for header in [sshPacket, { webPacket with destinationPort := 80 },
      { webPacket with protocol := Protocol.udp }, ⟨0, 0, Protocol.icmp, 0, 53⟩] do
    ensure (!compiled.rules.allows header) "A forbidden or unspecified packet was admitted."
  let reversed ← unwrap (compile policy.reverse)
  ensure (Partition.checkACLRefines compiled.rules reversed.rules &&
    Partition.checkACLRefines reversed.rules compiled.rules)
    "Declarative policy meaning depended on requirement order."

private def conflictTests : IO Unit := do
  let allowTcp : Intent := ⟨"ALLOW-TCP", { protocol := some Protocol.tcp }, .permit⟩
  for intents in [[allowTcp, denySsh], [denySsh, allowTcp]] do
    match compile intents with
    | .ok _ => throw (IO.userError "An overlapping permit and prohibition compiled.")
    | .error (.conflict conflict) =>
      ensure (conflict.permitted.id == "ALLOW-TCP" && conflict.forbidden.id == "DENY-SSH")
        "The conflict lost its source requirement IDs."
      ensure (conflict.permitted.test.accepts conflict.header &&
        conflict.forbidden.test.accepts conflict.header) "The conflict packet does not match both requirements."
      ensure (conflict.header.protocol == Protocol.tcp && conflict.header.destinationPort == 22)
        "The conflict did not identify a concrete SSH packet."
    | .error error => throw (IO.userError s!"Expected a conflict: {error.describe}")
  let atMaximum : List Intent := [
    ⟨"ALLOW-MAX", { source := some ⟨4294967295, 32⟩ }, .permit⟩,
    ⟨"DENY-ALL", {}, .deny⟩]
  match compile atMaximum with
  | .error (.conflict conflict) =>
    ensure (conflict.header.source == 4294967295) "The maximum-address conflict was missed."
  | _ => throw (IO.userError "The full-width address conflict was not reported.")

private def edgeCaseTests : IO Unit := do
  expectInvalid [] .emptyPolicy
  expectInvalid [⟨"", https, .permit⟩] (.invalidId "")
  expectInvalid [⟨" ", https, .permit⟩] (.invalidId " ")
  expectInvalid [⟨"BAD\nID", https, .permit⟩] (.invalidId "BAD\nID")
  expectInvalid [allowHttps, { denySsh with id := allowHttps.id }] (.duplicateId allowHttps.id)
  let forbiddenOnly ← unwrap (compile [denySsh])
  ensure (forbiddenOnly.rules.isEmpty) "A forbidden-only policy should use deny default."
  ensure (forbiddenOnly.requirementIds == ["DENY-SSH"]) "A prohibition ID was discarded."
  ensure (!forbiddenOnly.rules.allows webPacket && !forbiddenOnly.rules.allows sshPacket)
    "The forbidden-only policy admitted unspecified traffic."
  let empty : Match := { destinationPorts := some ⟨20, 10⟩ }
  let emptyOnly ← unwrap (compile [⟨"EMPTY", empty, .permit⟩])
  ensure (!emptyOnly.rules.allows webPacket && !emptyOnly.rules.allows sshPacket)
    "An empty permitted class admitted a packet."
  let emptyDenial ← unwrap (compile [allowHttps, ⟨"EMPTY-DENIAL", empty, .deny⟩])
  ensure (emptyDenial.rules.allows webPacket) "An empty prohibition created a conflict."
  let cells := (partition policy).cellCount
  for budget in [0, cells - 1] do
    match compile policy budget with
    | .error (.exhausted required actual) =>
      ensure (required == cells && actual == budget) "The budget error lost its resource counts."
    | _ => throw (IO.userError "An insufficient compilation budget produced an answer.")
  let exact ← unwrap (compile policy cells)
  ensure (exact.rules.allows webPacket) "An exact compilation budget did not complete."

def run : IO Unit := do
  policyTests
  conflictTests
  edgeCaseTests
  IO.println "ACL compiler tests passed."

end NetlibTest.ACLCompiler
