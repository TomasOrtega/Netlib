import Netlib.Examples.WireNATDeployment
import Netlib.Check.WireForwarding

namespace NetlibTest.WireNATDeployment

open Netlib Packet Protocol
open Netlib.Examples

private def context : Context := ⟨"alice", "application", "authority"⟩
private def scope : Scope := ⟨"reports", "read"⟩
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def authentication : List EAPSession.Event := [
  .authentication .begin, .authentication (.server (.request 7 13 [32])),
  .authentication (.peer (.response 7 13 [0])), .authentication (.server (.success 7)),
  .authentication (.method ⟨1, context.consumer, 13, true, some "SYNTHETIC trusted method result"⟩),
  .application (.install token)]
private def session : EAPSession.State := EAPSession.run context EAPSession.State.initial authentication
private theorem session_safe : session.Safe context := EAPSession.run_safe _ _ _ (EAPSession.initial_safe _)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def requestClass : Match := {
  source := some ⟨original.source, 32⟩
  destination := some ⟨translated.destination, 32⟩
  protocol := some Packet.Protocol.udp
  sourcePorts := some (PortRange.single original.sourcePort)
  destinationPorts := some (PortRange.single translated.destinationPort) }
private def replyClass : Match := {
  source := some ⟨translated.destination, 32⟩
  destination := some ⟨original.source, 32⟩
  protocol := some Packet.Protocol.udp
  sourcePorts := some (PortRange.single translated.destinationPort)
  destinationPorts := some (PortRange.single original.sourcePort) }
private def requirements : List Compile.SessionFirewall.Intent :=
  [⟨"REQUEST", scope, requestClass⟩, ⟨"REPLY", scope, replyClass⟩]
private def routes : List (Routing.Entry String) := [Routing.defaultRoute (some "service")]

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def build (state : EAPSession.State) : IO (Compile.SessionFirewall.Certified context state requirements) :=
  match Compile.SessionFirewall.compile context state requirements with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError error.describe)

private structure Captured where
  bytes : List UInt8
  checked : Check.Wire.Checked bytes

private def capture (header : Header) (payload : List UInt8) (ttl : UInt8 := 64) (omitted : Bool := false) : IO Captured := do
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, payload⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let udp ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨0x28, 0x4321, true, ttl, header.protocol, header.source, header.destination, udp⟩
  let bytes ← unwrap (IPv4.encode ip)
  let bytes := Import.EthernetIPv4.encode ⟨⟨2, 0, 0, 0, 0xea, 1⟩, ⟨2, 0, 0, 0, 0xea, 2⟩, bytes⟩
  return ⟨bytes, ← unwrap (Check.Wire.checkBytes bytes)⟩

private def load (value : Except WireForwarding.Error α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error.describe)

private def atIndex (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Missing native wire NAT fixture element {index}.")

private def roundtrip (omitted : Bool) (payload : List UInt8) : IO Unit := do
  let compiled ← build session
  let active := SessionFirewallDeployment.pipeline compiled routes [] .permit
  let captured ← capture original payload 64 omitted
  let checked := captured.checked
  let entry : NetfilterNAT.Entry := ⟨⟨checked.header, translated.reverse, 0, 0, 0⟩, true, true⟩
  match accepted : WireForwarding.step active ConntrackLifecycle.State.initial (WireNATDeployment.input checked 0 (some entry)) with
  | .error error => throw (IO.userError error.describe)
  | .ok outcome =>
    match forwarded : outcome.output with
    | none => throw (IO.userError "The synthetic current scope must permit its translated request.")
    | some emission =>
      have _ := WireNATDeployment.output_current_permission compiled session_safe active
        (SessionFirewallDeployment.pipeline_equivalent compiled routes [] .permit) checked 0 (some entry)
        ConntrackLifecycle.State.initial outcome accepted emission forwarded
      let decoded ← unwrap (UDP.decodeIPv4 emission.bytes)
      ensure (decoded.header == translated && decoded.datagram.payload == payload && decoded.ip.packet.ttl == 63 &&
          decoded.ip.packet.tos == 0x28 && decoded.ip.packet.identification == 0x4321 && decoded.ip.packet.dontFragment &&
          requestClass.accepts outcome.afterDestination && !requestClass.accepts checked.header &&
          !requestClass.accepts decoded.header && decide (decoded.datagram.checksum = 0 ↔ omitted = true))
        "The checked input bytes must pass the computed post-DNAT scope and emit a complete payload-preserving SNAT packet."
      let reply ← capture translated.reverse (payload ++ [42]) 64 omitted
      let returned ← load (WireForwarding.step active outcome.state (WireNATDeployment.input reply.checked 0 none))
      match returned.output with
      | none => throw (IO.userError "The matching reply scope must permit reverse translation.")
      | some replyEmission =>
        let decodedReply ← unwrap (UDP.decodeIPv4 replyEmission.bytes)
        ensure (decodedReply.header == original.reverse && decodedReply.datagram.payload == payload ++ [42] &&
            decodedReply.ip.packet.ttl == 63 && replyClass.accepts returned.afterDestination &&
            returned.attachment.classification == .established && returned.state.records.all (·.seenReply))
          "The exact wire reply must use the cached inverse binding, current reply scope, and its own preserved payload."
      let loggedOff := EAPSession.step context session (.authentication .logoff)
      let denied ← build loggedOff
      let denyPipeline := SessionFirewallDeployment.pipeline denied routes [] .permit
      let blocked ← load (WireForwarding.step denyPipeline returned.state (WireNATDeployment.input checked 0 none))
      ensure (blocked.output.isNone && blocked.disposition == .forwardDrop && blocked.state == returned.state &&
          blocked.attachment.classification == .established)
        "A regenerated post-Logoff filter must block bytes from the same established binding without deleting it."
      let stale ← load (WireForwarding.step active returned.state (WireNATDeployment.input checked 0 none))
      ensure (stale.output.isSome && !loggedOff.auth.authorized)
        "A stale allow snapshot can still emit valid bytes; current installation remains an explicit premise."

private def ttlTests : IO Unit := do
  let compiled ← build session
  let active := SessionFirewallDeployment.pipeline compiled routes [] .permit
  for ttl in ([0, 1, 2] : List UInt8) do
    let captured ← capture original [1, 2, 3] ttl
    let checked := captured.checked
    let entry : NetfilterNAT.Entry := ⟨⟨checked.header, translated.reverse, 0, 0, 0⟩, true, true⟩
    let result ← load (WireForwarding.step active ConntrackLifecycle.State.initial (WireNATDeployment.input checked 0 (some entry)))
    if ttl.toNat ≤ 1 then
      ensure (result.output.isNone && result.disposition == .ttlExpired && result.state.records.isEmpty &&
          result.lifecycle.isNone && result.afterSource.isNone)
        "A routed fresh packet with expired TTL must not filter, source-translate, emit, or confirm its candidate."
    else
      match result.output with
      | none => throw (IO.userError "A TTL of two must allow one modeled forwarding step.")
      | some emission =>
        ensure ((← unwrap (UDP.decodeIPv4 emission.bytes)).ip.packet.ttl == 1)
          "Forwarded bytes must contain the actual decremented TTL and valid regenerated checksums."

private def nativeFindingTest : IO Unit := do
  let session ← unwrap (Check.SessionFirewall.Input.parse (← IO.FS.readFile "examples/wire-nat/session.json"))
  let sessionReport ← unwrap session.check
  if compliant : sessionReport.compliant = true then
    let attached ← atIndex sessionReport.findings.attach 2
    let finding := attached.val
    let replay ← unwrap (Check.WireForwarding.Input.parse (← IO.FS.readFile "examples/wire-nat/replay.json"))
    let replayReport ← unwrap replay.check
    ensure replayReport.compliant "The complete native NAT replay must match before selecting its admission finding."
    let prior ← unwrap (Check.WireForwarding.audit replay.routing replay.initial (replay.events.take 2))
    let selected ← atIndex replay.events 2
    match selected.event with
    | .erase .. => throw (IO.userError "The selected native admission event must contain packet bytes.")
    | .packet config zone packet observed _ =>
      let candidate := (Check.WireForwarding.packetInput prior.final config zone packet).candidate
      let active := SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall replay.routing.compile
        config.late.compile config.late.policy
      match accepted : WireForwarding.step active prior.final (WireNATDeployment.input packet.checked zone candidate) with
      | .error error => throw (IO.userError error.describe)
      | .ok outcome =>
        match forwarded : outcome.output with
        | none => throw (IO.userError "The checked native admission finding must produce its selected UDP output.")
        | some emission =>
          have _ := WireNATDeployment.checked_output_current_permission sessionReport compliant finding attached.property
            packet.checked zone candidate replay.routing.compile config.late.compile config.late.policy
            prior.final outcome accepted emission forwarded
          match observed.output with
          | none => throw (IO.userError "The native admission observation must retain its independently captured output.")
          | some output =>
            ensure (Check.WireForwarding.emissionValue emission == output.value &&
                emission.decoded.datagram.payload == packet.checked.packet.datagram.payload &&
                emission.decoded.ip.packet.ttl.toNat + 1 == packet.checked.packet.ip.packet.ttl.toNat)
              "The actual native finding must connect decoded input, computed NAT output, exact payload, TTL, and current session permission."
  else throw (IO.userError "The native session firewall snapshots must match their current EAP-derived scope policies.")

def run : IO Unit := do
  for omitted in [false, true] do
    roundtrip omitted [1, 2, 3]
    roundtrip omitted [1, 2, 3, 4]
  ttlTests
  nativeFindingTest
  IO.println "Checked wire NAT and session deployment tests passed."

end NetlibTest.WireNATDeployment
