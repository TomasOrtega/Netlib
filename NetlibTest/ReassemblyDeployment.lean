import Netlib.Examples.ReassemblyDeployment

namespace NetlibTest.ReassemblyDeployment

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
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩
private def requestClass : Match := {
  source := some ⟨original.source, 32⟩
  destination := some ⟨translated.destination, 32⟩
  protocol := some Packet.Protocol.udp
  sourcePorts := some (PortRange.single original.sourcePort)
  destinationPorts := some (PortRange.single translated.destinationPort) }
private def requirements : List Compile.SessionFirewall.Intent := [⟨"REQUEST", scope, requestClass⟩]
private def routes : List (Routing.Entry String) := [Routing.defaultRoute (some "service")]

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

private def pipeline (compiled : Compile.SessionFirewall.Certified context state requirements) : ReassemblyForwarding.Pipeline :=
  ⟨⟨SessionFirewallDeployment.pipeline compiled routes [] .permit, fun _ => ⟨1500, by decide⟩⟩, fun _ _ => entry⟩

private def family (header : Header) (omitted : Bool) (limit : IPv4Refragmentation.Budget) :
    IO (List IPv4Fragment.Decoded) := do
  let data := List.replicate 100 (170 : UInt8)
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, data⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort data
  let payload ← unwrap (UDP.encode header.source header.destination datagram)
  let packet : IPv4.Packet := ⟨40, 4317, false, 64, header.protocol, header.source, header.destination, payload⟩
  return (← unwrap (IPv4Refragmentation.checkGenerated packet limit false)).fragments

private def arrival (now : Nat) (fragment : IPv4Fragment.Decoded) : ReassemblyForwarding.Input :=
  ⟨now, ⟨65536, 0⟩, 0, fragment⟩

private def exercise (omitted : Bool) : IO Unit := do
  let compiled ← build session
  let active := pipeline compiled
  let parts ← family original omitted ⟨68, by decide⟩
  let [first, middle, last] := parts | throw (IO.userError "Expected three synthetic source fragments.")
  let firstResult ← unwrap (ReassemblyForwarding.step active ⟨30⟩ .initial (arrival 1 first))
  let middleResult ← unwrap (ReassemblyForwarding.step active ⟨30⟩ firstResult.state (arrival 2 middle))
  match accepted : ReassemblyForwarding.step active ⟨30⟩ middleResult.state (arrival 3 last) with
  | .error error => throw (IO.userError error)
  | .ok result =>
    match completed : result.completed with
    | none => throw (IO.userError "The final fragment must complete the datagram.")
    | some packet =>
      match forwarded : packet.outcome.output with
      | none => throw (IO.userError "The synthetic current credential must authorize its complete datagram.")
      | some emission =>
        have _ := ReassemblyDeployment.step_current_permission compiled session_safe active
          (SessionFirewallDeployment.pipeline_equivalent compiled routes [] .permit) ⟨30⟩ middleResult.state
          (arrival 3 last) result packet accepted completed emission forwarded
        ensure (emission.target == translated && packet.outcome.sizeCap.map (·.val) == some 68 &&
            requestClass.accepts packet.outcome.afterDestination &&
            emission.decoded.datagram.payload == List.replicate 100 170 &&
            (emission.decoded.datagram.checksum == 0) == omitted)
          "Reassembled synthetic EAP traffic must use its post-DNAT scope and preserve payload and checksum omission."
        let replies ← family translated.reverse omitted ⟨1500, by decide⟩
        let [reply] := replies | throw (IO.userError "Expected a whole synthetic reply.")
        let marked ← unwrap (ReassemblyForwarding.step active ⟨30⟩ result.state (arrival 4 reply))
        ensure (marked.state.conntrack.records.all (·.seenReply))
          "A reply must update the cached seen-reply state before the Logoff scenario."
        let beforeLogoff ← unwrap (ReassemblyForwarding.step active ⟨30⟩ marked.state (arrival 5 first))
        let waiting ← unwrap (ReassemblyForwarding.step active ⟨30⟩ beforeLogoff.state (arrival 6 middle))
        let loggedOff := EAPSession.step context session (.authentication .logoff)
        let denied ← build loggedOff
        let blockedPipeline := pipeline denied
        match blocked : ReassemblyForwarding.step blockedPipeline ⟨30⟩ waiting.state (arrival 7 last) with
        | .error error => throw (IO.userError error)
        | .ok output =>
          match completion : output.completed with
          | none => throw (IO.userError "Deny must act on the completed datagram rather than preserve buffering.")
          | some packet =>
            have _ : packet.outcome.output = none := by
              obtain ⟨prepared, _, _, _, _, _, processed, _, _⟩ :=
                Check.ReassemblyForwarding.step_completed blockedPipeline ⟨30⟩ waiting.state (arrival 7 last)
                  output packet blocked completion
              exact ReassemblyDeployment.postlogoff_output_none context session session_safe denied blockedPipeline
                (SessionFirewallDeployment.pipeline_equivalent denied routes [] .permit) packet.reassembled packet.source
                packet.wire packet.same prepared packet.outcome processed
            ensure (packet.outcome.output.isNone && packet.outcome.disposition == .forwardDrop &&
                packet.outcome.attachment.classification == .established &&
                output.state.conntrack == waiting.state.conntrack && output.state.fragments.queues.isEmpty)
              "Logoff before completion must deny the complete family and retain the established NAT binding."
        let stale ← unwrap (ReassemblyForwarding.step active ⟨30⟩ waiting.state (arrival 7 last))
        ensure ((stale.completed.map (·.outcome.output.isSome)).getD false && !loggedOff.auth.authorized)
          "A stale installed allow filter remains a deployment risk; synchronous installation is an explicit premise."

def run : IO Unit := do
  exercise false
  exercise true
  IO.println "Ingress reassembly and EAP completion-time permission tests passed."

end NetlibTest.ReassemblyDeployment
