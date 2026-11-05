import Netlib.Examples.MTUDeployment

namespace NetlibTest.MTUDeployment

open Netlib Packet Protocol Examples

private def context : Context := ⟨"alice", "application", "authority"⟩
private def scope : Scope := ⟨"reports", "read"⟩
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def session : EAPSession.State := EAPSession.run context EAPSession.State.initial [
  .authentication .begin, .authentication (.server (.request 7 13 [32])),
  .authentication (.peer (.response 7 13 [0])), .authentication (.server (.success 7)),
  .authentication (.method ⟨1, context.consumer, 13, true, some "SYNTHETIC trusted method result"⟩),
  .application (.install token)]
private theorem session_safe : session.Safe context := EAPSession.run_safe _ _ _ (EAPSession.initial_safe _)
private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def requestClass : Match := {
  source := some ⟨original.source, 32⟩
  destination := some ⟨wire.destination, 32⟩
  protocol := some Packet.Protocol.udp
  sourcePorts := some (PortRange.single original.sourcePort)
  destinationPorts := some (PortRange.single wire.destinationPort) }
private def requirements : List Compile.SessionFirewall.Intent := [⟨"REQUEST", scope, requestClass⟩]
private def mtu : MTUForwarding.MTU := ⟨68, by decide⟩
private def routes : List (Routing.Entry String) := [Routing.defaultRoute (some "service")]

example (emission : MTUForwarding.Emission input) :
    IPv4Fragmentation.reassemble emission.fragments.fragments = .ok emission.transit.decoded.ip.packet :=
  (MTUDeployment.output_facts emission).reassembled

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def load (result : Except MTUForwarding.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def build (state : EAPSession.State) : IO (Compile.SessionFirewall.Certified context state requirements) :=
  match Compile.SessionFirewall.compile context state requirements with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError error.describe)

private structure Captured where
  bytes : List UInt8
  checked : Check.Wire.Checked bytes

private def capture (header : Header) (ttl : UInt8) (omitted : Bool) : IO Captured := do
  let payload : List UInt8 := List.replicate 100 170
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, payload⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let udp ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨0x28, 0x4321, false, ttl, header.protocol, header.source, header.destination, udp⟩
  let ip ← unwrap (IPv4.encode ip)
  let bytes := Import.EthernetIPv4.encode ⟨⟨2, 0, 0, 0, 0xea, 1⟩, ⟨2, 0, 0, 0, 0xea, 2⟩, ip⟩
  return ⟨bytes, ← unwrap (Check.Wire.checkBytes bytes)⟩

private def roundtrip (omitted : Bool) : IO Unit := do
  let compiled ← build session
  let active : MTUForwarding.Pipeline := ⟨SessionFirewallDeployment.pipeline compiled routes [] .permit, fun _ => mtu⟩
  let captured ← capture original 64 omitted
  let checked := captured.checked
  match accepted : MTUForwarding.step active ConntrackLifecycle.State.initial (MTUDeployment.input checked 0 (some entry)) with
  | .error error => throw (IO.userError error.describe)
  | .ok outcome =>
    match forwarded : outcome.output with
    | none => throw (IO.userError "The synthetic current scope must allow its complete datagram before fragmentation.")
    | some emission =>
      have _ := MTUDeployment.output_current_permission compiled session_safe active
        (SessionFirewallDeployment.pipeline_equivalent compiled routes [] .permit) checked 0 (some entry)
        ConntrackLifecycle.State.initial outcome accepted emission forwarded
      let rebuilt ← unwrap (IPv4Fragmentation.reassemble emission.fragments.fragments.reverse)
      let datagram ← unwrap (UDP.decode rebuilt.source rebuilt.destination rebuilt.payload)
      ensure (emission.fragments.fragments.length == 3 && outcome.state.records.length == 1 &&
          emission.transit.target == wire && requestClass.accepts outcome.afterDestination &&
          !requestClass.accepts checked.header && !requestClass.accepts emission.transit.target &&
          datagram.payload == checked.packet.datagram.payload && rebuilt.ttl == 63 &&
          rebuilt.tos == 0x28 && rebuilt.identification == 0x4321 && (datagram.checksum == 0) == omitted)
        "A SYNTHETIC EAP-scoped datagram must pass the post-DNAT class once and reassemble after NAT with unchanged application payload."
      let reply ← capture wire.reverse 1 omitted
      let marked ← load (MTUForwarding.step active outcome.state (MTUDeployment.input reply.checked 0 none))
      ensure (marked.disposition == .ttlExpired && marked.state.records.all (·.seenReply))
        "A TTL-expired reply must establish the cached classification before testing current post-Logoff policy."
      let loggedOff := EAPSession.step context session (.authentication .logoff)
      let denied ← build loggedOff
      let blockedPipeline : MTUForwarding.Pipeline :=
        ⟨SessionFirewallDeployment.pipeline denied routes [] .permit, fun _ => mtu⟩
      match blocked : MTUForwarding.step blockedPipeline marked.state (MTUDeployment.input checked 0 none) with
      | .error error => throw (IO.userError error.describe)
      | .ok result =>
        have _ := MTUDeployment.postlogoff_output_none context session session_safe denied blockedPipeline
          (SessionFirewallDeployment.pipeline_equivalent denied routes [] .permit) checked 0 none marked.state result blocked
        ensure (result.output.isNone && result.disposition == .forwardDrop && result.state == marked.state &&
            result.attachment.classification == .established)
          "A current post-Logoff filter must deny the entire fragment family from the unchanged established binding."
      let stale ← load (MTUForwarding.step active marked.state (MTUDeployment.input checked 0 none))
      ensure (stale.output.isSome && !loggedOff.auth.authorized)
        "A stale installed allow policy can still emit fragments; current policy installation is an explicit premise."

def run : IO Unit := do
  roundtrip false
  roundtrip true
  IO.println "MTU fragmentation and current session deployment tests passed."

end NetlibTest.MTUDeployment
