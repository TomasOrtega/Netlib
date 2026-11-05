import Netlib.Examples.SafeHandoffDeployment

namespace NetlibTest.SafeHandoffDeployment

open Netlib Packet Protocol Examples
open StatefulFailover (Gateway)

private def context : Context := ⟨"alice", "application", "authority"⟩
private def scope : Scope := ⟨"reports", "read"⟩
private def credential : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def session : EAPSession.State := EAPSession.run context EAPSession.State.initial [
  .authentication .begin, .authentication (.server (.request 7 13 [32])),
  .authentication (.peer (.response 7 13 [0])), .authentication (.server (.success 7)),
  .authentication (.method ⟨1, context.consumer, 13, true, some "SYNTHETIC trusted method result"⟩),
  .application (.install credential)]
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

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private structure Call (before : SafeHandoff.State) (event : SafeHandoff.Event) where
  result : SafeHandoff.Result
  computed : SafeHandoff.step before event = .ok result

private def invoke (before : SafeHandoff.State) (event : SafeHandoff.Event) : IO (Call before event) :=
  match computed : SafeHandoff.step before event with
  | .error message => throw (IO.userError message)
  | .ok result => pure ⟨result, computed⟩

private def compile (state : EAPSession.State) : IO (Compile.SessionFirewall.Certified context state requirements) :=
  match Compile.SessionFirewall.compile context state requirements with
  | .error message => throw (IO.userError message.describe)
  | .ok compiled => pure compiled

private def configuration (id : String) (compiled : Compile.SessionFirewall.Certified context state requirements) :
    SafeHandoff.Configuration := ⟨id, SessionFirewallDeployment.pipeline compiled routes [] .permit⟩

private def source (header : Header) (omitted : Bool) : IO SafeHandoff.Source := do
  let data : List UInt8 := [0, 255, 17, 0, 41]
  let datagram := if omitted then (⟨header.sourcePort, header.destinationPort, 0, data⟩ : UDP.Datagram)
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort data
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let packet : IPv4.Packet := ⟨16, 1547, false, 64, Packet.Protocol.udp, header.source, header.destination, transport⟩
  let bytes ← unwrap (IPv4.encode packet)
  match decoded : UDP.decodeIPv4 bytes with
  | .error message => throw (IO.userError message)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private theorem installed_configuration {before : SafeHandoff.State} {gateway : Gateway}
    {value : SafeHandoff.Configuration} (call : Call before (.install gateway value)) (selected : Gateway) :
    call.result.state.configurations selected =
      if selected = gateway then value else before.configurations selected := by
  obtain ⟨_, raw, computed, same⟩ := SafeHandoff.step_core _ _ _ call.computed
  rw [show call.result.state = raw.state from congrArg SafeHandoff.RawResult.state same]
  exact SafeHandoff.core_install_configuration _ _ _ _ computed _

private def exercise (omitted : Bool) : IO Unit := do
  let allowed ← compile session
  let request ← source original omitted
  let reply ← source translated.reverse omitted
  let active := configuration "authenticated" allowed
  let initial := SafeHandoff.State.initial active active
  let first ← invoke initial (.establish ⟨0, request.packet, some entry⟩)
  ensure (first.result.established.any (fun packet => packet.outcome.output.isSome))
    "The initial certified credential must permit the actual source NAT flow."
  let staged ← invoke first.result.state (.stage 0 original)
  let warm ← invoke staged.result.state (.commit 180)
  let oldRequest ← invoke warm.result.state (.assign .original request)
  let oldReply ← invoke oldRequest.result.state (.assign .reply reply)
  let client ← invoke oldReply.result.state (.handoff .client .standby)
  let server ← invoke client.result.state (.handoff .server .standby)
  let loggedOff := EAPSession.step context session (.authentication .logoff)
  let stale ← invoke server.result.state (.serve 0)
  ensure (!loggedOff.auth.authorized && stale.result.served.any (fun served => served.outcome.output.isSome))
    "A stale installed credential policy still permits queued traffic; current installation remains an explicit premise."
  let denied ← compile loggedOff
  let blocked := configuration "logged-off" denied
  let installA ← invoke server.result.state (.install .primary blocked)
  let installB ← invoke installA.result.state (.install .standby blocked)
  have allInstalled : ∀ selected, installB.result.state.configurations selected = blocked := by
    intro selected
    rw [installed_configuration installB selected]
    cases selected
    · simp only [reduceCtorEq, ite_false]
      rw [installed_configuration installA .primary]
      rfl
    · rfl
  let deniedReply ← invoke installB.result.state (.serve 1)
  match stored : deniedReply.result.served with
  | none => throw (IO.userError "The admitted old-route reply must have an actual processing result.")
  | some served =>
    have installed : SessionFirewallDeployment.ForwardEquivalent
        (installB.result.state.configurations served.ticket.value.gateway).pipeline denied := by
      rw [allInstalled]
      exact SessionFirewallDeployment.pipeline_equivalent denied routes [] .permit
    have _ := SafeHandoffDeployment.postlogoff_output_none context session session_safe denied
      installB.result.state 1 deniedReply.result served deniedReply.computed stored installed
    ensure (served.outcome.output.isNone && served.outcome.disposition == .forwardDrop &&
      served.outcome.attachment.classification == .established &&
      deniedReply.result.state.outstanding .primary == 1 &&
      deniedReply.result.state.gateways.primary.records.all (·.seenReply))
      "Logoff must deny the queued old-route reply while retaining its seen-reply update and the older request."
  let deniedRequest ← invoke deniedReply.result.state (.serve 0)
  ensure (deniedRequest.result.served.any (fun served => served.outcome.output.isNone &&
      served.outcome.attachment.classification == .established) &&
    deniedRequest.result.state.work.pending.isEmpty && deniedRequest.result.state.work.completed.map (·.id) == [1, 0])
    "The older admitted request must encounter current deny after the reply update, without retaining old permission."
  let fenced ← invoke deniedRequest.result.state (.fence .primary)
  ensure (fenced.result.state.gateways.isFenced .primary)
    "Denied processing still retires exact tickets and permits the safe final fence."

def run : IO Unit := do
  exercise false
  exercise true
  IO.println "Outstanding handoff and current EAP permission tests passed."

end NetlibTest.SafeHandoffDeployment
