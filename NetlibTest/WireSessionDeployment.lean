import Netlib.Examples.WireSessionDeployment

namespace NetlibTest.WireSessionDeployment

open Netlib Packet Protocol
open Netlib.Examples

example (checked : Check.Wire.Checked bytes) : WireSessionDeployment.reencode checked = .ok bytes :=
  WireSessionDeployment.reencode_exact checked

example (checked : Check.Wire.Checked bytes) (present : checked.packet.datagram.checksum ≠ 0) :
    InternetChecksum.valid (UDP.pseudoHeader checked.packet.ip.packet.source checked.packet.ip.packet.destination
      checked.packet.datagram.lengthWord ++ checked.packet.ip.packet.payload) = true :=
  WireSessionDeployment.udp_checksum checked present

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def atIndex (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Missing wire deployment fixture element {index}.")

private def rawAt (index : Nat) : IO (List UInt8) := do
  let lines := (← IO.FS.readFile "examples/wire/native/data-frames.jsonl").splitOn "\n" |>.filter (!·.isEmpty)
  let row ← unwrap (Import.Json.parse (← atIndex lines index))
  unwrap (Import.EAPOL.bytesFromHex (← unwrap ((← unwrap (row.getObjVal? "hex")).getStr?)))

def run : IO Unit := do
  let bytes ← rawAt 2
  let checked ← unwrap (Check.Wire.checkBytes bytes)
  ensure (checked.header == (Header.mk 3221225986 3325256706 Packet.Protocol.udp 41000 9000) &&
      checked.packet.datagram.payload == "admission:credential-permitted:request".toUTF8.toList &&
      checked.packet.datagram.checksum != 0 && (← unwrap checked.encode) == bytes)
    "The actual permitted-stage capture must supply its exact tuple, payload, checksum, and reconstructed bytes."
  let input ← unwrap (Check.SessionFirewall.Input.parse (← IO.FS.readFile "examples/wire/bundle.json"))
  let report ← unwrap input.check
  if compliant : report.compliant = true then
    let attached ← atIndex report.findings.attach 2
    let finding := attached.val
    let routes := [Routing.defaultRoute (some "service")]
    let active := SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall routes [] .permit
    let entry : NetfilterNAT.Entry := ⟨⟨checked.header, checked.header.reverse, 0, 0, 0⟩, false, false⟩
    let tracker : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
    let packet : ConntrackLifecycle.Input := ⟨0, checked.header, none⟩
    match accepted : ConntrackLifecycle.step active tracker packet with
    | .error error => throw (IO.userError error.describe)
    | .ok outcome =>
      if forwarded : outcome.output = some checked.header then
        if stage : outcome.afterDestination = checked.header then
          have _ := WireSessionDeployment.checked_output_current_permission report compliant finding attached.property
            checked routes [] .permit tracker packet outcome checked.header accepted forwarded stage
          ensure (outcome.attachment.classification == .established && !outcome.attachment.fresh &&
              finding.checkpoint.firewall.permits .established checked.header)
            "The explicitly synthetic cached attachment must pass the actual checked native forward snapshot."
        else throw (IO.userError "The wire-to-forward-stage association must be explicit and exact.")
      else throw (IO.userError "The checked current snapshot must permit the decoded request tuple.")
    let denied ← atIndex report.findings 3
    match ConntrackLifecycle.step
        (SessionFirewallDeployment.snapshotPipeline denied.checkpoint.firewall routes [] .permit) tracker packet with
    | .error error => throw (IO.userError error.describe)
    | .ok outcome =>
      ensure (outcome.output.isNone && outcome.disposition == .forwardDrop && outcome.state == tracker)
        "The post-Logoff snapshot must deny the same decoded tuple while the synthetic cached binding remains present."
  else throw (IO.userError "The fresh wire capture's checked session snapshot bundle must be compliant.")
  IO.println "Decoded wire session deployment tests passed."

end NetlibTest.WireSessionDeployment
