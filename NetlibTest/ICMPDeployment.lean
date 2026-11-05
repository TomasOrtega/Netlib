import Netlib.Examples.ICMPDeployment

namespace NetlibTest.ICMPDeployment

open Netlib Packet Protocol Examples

private def context : Protocol.Context := ⟨"alice", "application", "authority"⟩
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
  destinationPorts := some (PortRange.single wire.destinationPort) }
private def requirements : List Compile.SessionFirewall.Intent := [⟨"REQUEST", scope, requestClass⟩]
private def mtu : MTUForwarding.MTU := ⟨600, by decide⟩
private def reverseMTU : MTUForwarding.MTU := ⟨68, by decide⟩
private def routes : List (Routing.Entry String) := [Routing.defaultRoute (some "service")]
private def control : ICMPForwarding.Context :=
  ⟨fun _ => some ⟨"return", 3221225985, reverseMTU, 32⟩, [],
    [⟨{}, some [.related], .permit⟩], .deny, [⟨{}, some [.related], .permit⟩], .deny⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def build (state : EAPSession.State) : IO (Compile.SessionFirewall.Certified context state requirements) :=
  match Compile.SessionFirewall.compile context state requirements with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError error.describe)

private structure Captured where
  bytes : List UInt8
  checked : Check.Wire.Checked bytes

private def capture (size : Nat) (df : Bool) (ttl : UInt8) : IO Captured := do
  let datagram := UDP.computed original.source original.destination original.sourcePort original.destinationPort
    (List.replicate size 170)
  let udp ← unwrap (UDP.encode original.source original.destination datagram)
  let ip : IPv4.Packet := ⟨0x28, 0x4321, df, ttl, original.protocol, original.source, original.destination, udp⟩
  let bytes ← unwrap (IPv4.encode ip)
  let ethernet := Import.EthernetIPv4.encode ⟨⟨2, 0, 0, 0, 0xea, 1⟩, ⟨2, 0, 0, 0, 0xea, 2⟩, bytes⟩
  return ⟨ethernet, ← unwrap (Check.Wire.checkBytes ethernet)⟩

private def execute : IO Unit := do
  let granted ← build session
  let active : ICMPForwarding.Pipeline :=
    ⟨⟨SessionFirewallDeployment.pipeline granted routes [] .permit, fun _ => mtu⟩, control⟩
  let fitting ← capture 100 false 64
  match accepted : ICMPForwarding.step active ConntrackLifecycle.State.initial
      (ICMPDeployment.input fitting.checked 0 (some entry)) 1234 with
  | .error error => throw (IO.userError error.describe)
  | .ok outcome =>
    match forwarded : outcome.transit.output with
    | none => throw (IO.userError "The synthetic current scope must allow its UDP datagram.")
    | some emission =>
      have _ := ICMPDeployment.output_current_permission granted session_safe active
        (SessionFirewallDeployment.pipeline_equivalent granted routes [] .permit) fitting.checked 0 (some entry) false
        ConntrackLifecycle.State.initial 1234 outcome accepted emission forwarded
      ensure (outcome.control.output.isNone && emission.transit.target == wire)
        "Current scope permits post-DNAT UDP transit without creating a control error."
      let loggedOff := EAPSession.step context session (.authentication .logoff)
      let denied ← build loggedOff
      let blocked : ICMPForwarding.Pipeline :=
        ⟨⟨SessionFirewallDeployment.pipeline denied routes [] .permit, fun _ => mtu⟩, control⟩
      for capture in [fitting, ← capture 100 false 1, ← capture 601 true 64] do
        let checked := capture.checked
        match computed : ICMPForwarding.step blocked outcome.transit.state
            (ICMPDeployment.input checked 0 none) 1234 with
        | .error error => throw (IO.userError error.describe)
        | .ok result =>
          have noTransit := ICMPDeployment.postlogoff_transit_none context session session_safe denied blocked
            (SessionFirewallDeployment.pipeline_equivalent denied routes [] .permit) checked 0 none false
            outcome.transit.state 1234 result computed
          ensure (result.transit.output.isNone && !loggedOff.auth.authorized &&
              !loggedOff.session.permits context scope && result.transit.state == outcome.transit.state)
            "Logoff must deny UDP transit while retaining its existing tracking entry."
          if checked.packet.ip.packet.ttl == 1 || checked.packet.ip.packet.dontFragment then
            match sent : result.control.output with
            | none => throw (IO.userError "TTL and DF errors must remain possible before the current denying transit filter.")
            | some error =>
              have facts := ICMPDeployment.control_output_facts blocked outcome.transit.state
                (ICMPDeployment.input checked 0 none) 1234 result computed error sent
              have _ := facts.1.restored
              have _ := noTransit
              ensure (error.bytes.length == 68 && error.quote.packet == (IPv4Quote.make checked.packet 40).packet)
                "An actual post-Logoff control error must quote ingress exactly and fit the independent return route."
          else
            ensure (result.control.output.isNone && result.transit.disposition == .forwardDrop)
              "A fitting post-Logoff datagram must be filtered without generating an error."

def run : IO Unit := do
  execute
  IO.println "ICMP and current session deployment tests passed."

end NetlibTest.ICMPDeployment
