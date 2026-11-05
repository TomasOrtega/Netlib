import Netlib.Check.Conntrack

namespace NetlibTest.ConntrackAudit

open Netlib Packet Check.Conntrack

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError message)
  | .error _ => pure ()

example (compiled : Compile.ACL.Certified intents) (rows : List Row) :
    (audit compiled rows).compliant = true ↔
      ∀ row ∈ rows, Compile.ACL.Meaning intents row.flow.original :=
  (audit compiled rows).compliant_iff

def run : IO Unit := do
  let xml ← IO.FS.readFile "examples/conntrack/native/conntrack.xml"
  let raw ← IO.FS.readFile "examples/conntrack/native/netlink.json"
  let policy ← IO.FS.readFile "examples/conntrack/intent.json"
  let tcpOnly ← IO.FS.readFile "examples/conntrack/tcp-only.json"
  for text in [xml, raw] do
    let input ← unwrap (Input.parse text policy)
    let checked := input.check
    ensure (checked.compliant && checked.findings.length == 4)
      "The native flow policy audit lost records or rejected the declared service."
    ensure (decide (checked.findings.map Finding.row = input.snapshot.rows))
      "The audit reordered or changed its original source rows."
    let denied ← unwrap (Input.parse text tcpOnly)
    let findings := denied.check.findings
    ensure (!denied.check.compliant && (findings.filter (fun finding => !finding.passed)).length == 2)
      "The TCP-only policy did not identify both native UDP flows."
    for finding in findings do
      ensure (finding.passed == (finding.row.flow.original.protocol == Protocol.tcp))
        "Policy authority was inferred from native status instead of the original tuple."
    reject (Input.parse text policy 0) "An exhausted policy budget produced a passing flow audit."
  let original : Header := ⟨3221225986, 3325256706, Protocol.udp, 31000, 9000⟩
  let wire : Header := ⟨3405803777, 3325256706, Protocol.udp, 40000, 9000⟩
  let (associated, forward) ← unwrap (mapPacket raw 0 original)
  ensure associated "The native original tuple was not associated."
  let forwardPacket ← unwrap (Import.PacketFields.header (← unwrap (forward.getObjVal? "output")))
  ensure (forwardPacket == wire)
    "The native original tuple projected the wrong public endpoint."
  let (associated, returned) ← unwrap (mapPacket raw 0 wire.reverse)
  ensure associated "The native reply tuple was not associated."
  let returnPacket ← unwrap (Import.PacketFields.header (← unwrap (returned.getObjVal? "output")))
  ensure (returnPacket == original.reverse)
    "The native reply tuple did not restore its private endpoint."
  let (otherZone, _) ← unwrap (mapPacket raw 1 original)
  ensure (!otherZone) "Tuple lookup crossed a conntrack zone."
  let (wrongPeer, _) ← unwrap (mapPacket raw 0 { wire.reverse with source := 3325256708 })
  ensure (!wrongPeer) "An unrelated peer acquired a reported association."
  reject (mapPacket raw 65536 original) "An out-of-range zone was accepted."
  reject (mapPacket xml 0 original) "Partial XML status was used for a full-status native projection."
  reject (Input.parse "" policy) "Missing capture bytes were treated as a successful empty XML dump."
  IO.println "Reported conntrack policy and association tests passed."

end NetlibTest.ConntrackAudit
