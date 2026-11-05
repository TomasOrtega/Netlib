import Netlib.Protocol.IngressProbe
import Netlib.Protocol.IngressAttachment
import Netlib.Packet.IngressPolicy

namespace NetlibTest.IngressProbe
open Netlib Packet Protocol
namespace Model
export Netlib.Protocol.IngressProbe (State Input Result process)
end Model
open StatefulFailover (Gateway)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def payload : List UInt8 := [0, 255, 65, 0, 17]
private def permit : ConntrackLifecycle.Pipeline := {
  routes := [⟨⟨wire.destination, 32⟩, some "server"⟩, ⟨⟨original.source, 32⟩, some "client"⟩],
  forward := [], forwardDefault := .permit }
private def config : SafeHandoff.Configuration := ⟨"ordinary-permit", permit⟩
private def initial : Model.State := CampusWithdrawal.State.initial config config
private def context : Context := ⟨"verified-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def credential : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def authenticated : EAPSession.State := EAPSession.run context .initial [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨1, context.consumer, 13, true, some "selected method evidence"⟩),
  .application (.install credential)]

example (before : Model.State) (input : Model.Input) (binding : NetfilterNAT.Entry) (safe : before.Safe)
    (selected : before.handoff.binding = some binding)
    (unfenced : before.handoff.gateways.isFenced input.gateway = false)
    (ready : TrackedFlow.Ready (before.handoff.gateways.table input.gateway) binding)
    (header : input.source.packet.header = binding.flow.input input.direction) (candidate : input.candidate = none) :
    ∃ result, Model.process before input = .ok result :=
  Protocol.IngressProbe.protected_completes before input binding safe selected unfenced ready header candidate

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def source (header : Header) (ttl : UInt8 := 64) : IO SafeHandoff.Source := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let bytes ← unwrap (IPv4.encode ⟨32, 4321, true, ttl, Packet.Protocol.udp, header.source, header.destination, transport⟩)
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw (IO.userError error)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def operation (before : Model.State) (event : SafeHandoff.Event) : IO Model.State := do
  let result ← unwrap (CampusWithdrawal.step before (.operation event))
  pure result.state

private def staged (request : SafeHandoff.Source) : IO Model.State := do
  let first ← operation initial (.establish ⟨0, request.packet, some entry⟩)
  operation first (.stage 0 original)

private def warm (request : SafeHandoff.Source) : IO Model.State := do
  operation (← staged request) (.commit 180)

private def probe (before : Model.State) (input : Model.Input) : IO (Model.Result before input) := do
  let result ← unwrap (Model.process before input)
  ensure (result.state.check && result.state.handoff.work.pending.map (·.id) == before.handoff.work.pending.map (·.id) &&
    result.state.handoff.work.completed.map (·.id) == before.handoff.work.completed.map (·.id) &&
    result.state.handoff.work.nextID == before.handoff.work.nextID && result.state.handoff.binding == before.handoff.binding &&
    result.state.handoff.gateways.owners.client == before.handoff.gateways.owners.client &&
    result.state.handoff.gateways.owners.server == before.handoff.gateways.owners.server &&
    result.state.handoff.gateways.cache.map (·.sourceEpoch) == before.handoff.gateways.cache.map (·.sourceEpoch) &&
    result.state.archive == before.archive && result.state.withdrawn == before.withdrawn &&
    result.state.handoff.gateways.epoch == before.handoff.gateways.epoch + 1)
    "A direct probe must preserve ticket work, route ownership, binding, cache, and archive while recording one actual network operation."
  pure result

private def emitted (before : Model.State) (input : Model.Input) (result : Model.Result before input) (target : Header) : IO Unit := do
  let some output := result.outcome.output | throw (IO.userError "The routed permitted probe must emit actual bytes.")
  ensure (output.target == target && output.decoded.header == target && output.decoded.datagram.payload == payload &&
    output.decoded.ip.packet.ttl == 63 && output.decoded.ip.packet.tos == 32 && output.decoded.ip.packet.identification == 4321)
    "The actual probe must preserve complete payload and IP metadata through the selected NAT boundary with one TTL decrement."
  ensure ((← unwrap (UDP.decodeIPv4 output.bytes)) == output.decoded)
    "The emitted probe must retain valid IPv4 and UDP checksum bytes."

private def rejects (before : Model.State) (input : Model.Input) (expected : String) : IO Unit :=
  match Model.process before input with
  | .error message => ensure (message == expected) s!"Expected {expected}; got {message}."
  | .ok _ => throw (IO.userError "The unsupported or unavailable probe must not acquire a successful computation certificate.")

private def baseline (request : SafeHandoff.Source) : IO Unit := do
  ensure (authenticated.session.permits context scope)
    "The baseline retains actual modeled EAP completion and credential permission independently of ingress ownership."
  let headerOnly : Packet.IngressPolicy.Policy := { rules := [⟨none, {}, .permit⟩] }
  let expected : Packet.IngressPolicy.Policy := { rules := [⟨some 2, {}, .permit⟩] }
  ensure (headerOnly.allows 4 original && !(expected.allows 4 original))
    "An unsafe installed header-only guard can admit an impersonating ingress even though interface-bound intent rejects it."
  let input : Model.Input := ⟨.primary, .original, request, some entry⟩
  let result ← probe initial input
  emitted initial input result wire
  ensure (result.outcome.attachment.fresh && result.outcome.attachment.classification == .new &&
    result.state.handoff.gateways.primary == unreplied && result.state.handoff.gateways.standby == .initial &&
    result.state.handoff.binding.isNone && result.state.handoff.work.pending.isEmpty && result.state.handoff.work.nextID == 0)
    "Actual unprotected baseline processing must confirm the supplied fresh record without fabricating ownership or a route ticket."
  rejects initial ⟨.primary, .original, request, none⟩ "A new flow requires an explicit unconfirmed candidate."
  let wrong := { entry with flow := { entry.flow with original := { original with sourcePort := 41001 } } }
  rejects initial ⟨.primary, .original, request, some wrong⟩ "The candidate original tuple or zone does not match the input."

private def protectedProbes (request reply : SafeHandoff.Source) : IO Unit := do
  let beforeCommit ← staged request
  rejects beforeCommit ⟨.standby, .original, request, none⟩
    "A protected probe requires its ready binding, matching direction, and no fresh candidate."
  let ready ← warm request
  let firstTicket ← operation ready (.assign .original request)
  let pending ← operation firstTicket (.assign .reply reply)
  let foreignGateway : Model.Input := ⟨.standby, .original, request, none⟩
  let other ← probe pending foreignGateway
  emitted pending foreignGateway other wire
  ensure (other.state.handoff.gateways.owners.client == .primary && other.state.handoff.work.pending.map (·.id) == [0, 1])
    "A direct probe can use a ready non-owner gateway without consuming or changing legitimate route assignments."
  let forged : Model.Input := ⟨.primary, .reply, reply, none⟩
  let unguarded ← probe other.state forged
  emitted other.state forged unguarded original.reverse
  ensure (unguarded.state.handoff.gateways.primary == replied && unguarded.state.handoff.gateways.standby == unreplied &&
    unguarded.state.handoff.work.pending.map (·.id) == [0, 1])
    "A passed cached forged reply must retain its real seen-reply and NAT effects independently of pending tickets."
  let actualGuard : Packet.IngressPolicy.Policy := {}
  let stopped ← unwrap (IngressAttachment.precheck (actualGuard.allows 4 wire.reverse) other.state (fun state => do
    let outcome ← Model.process state forged
    pure (outcome.state, outcome.outcome.output.isSome)))
  match stopped with
  | .processed _ => throw (IO.userError "An actual early rejection must not run the direct ordinary probe.")
  | .rejected retained =>
    ensure (retained.handoff.gateways.primary == unreplied &&
      retained.handoff.gateways.standby == unreplied && retained.handoff.gateways.epoch == other.state.handoff.gateways.epoch)
      "Rejected direct probes must preserve both tables and the epoch without ordinary output or route-ticket retirement."
  rejects pending ⟨.primary, .original, request, some entry⟩
    "A protected probe requires its ready binding, matching direction, and no fresh candidate."
  let unrelated ← source { original with sourcePort := 41001 }
  rejects pending ⟨.primary, .original, unrelated, none⟩
    "A protected probe requires its ready binding, matching direction, and no fresh candidate."
  let deniedConfig : SafeHandoff.Configuration := ⟨"current-deny", { permit with forwardDefault := .deny }⟩
  let denied ← operation ready (.install .primary deniedConfig)
  let dropped ← probe denied forged
  ensure (dropped.outcome.output.isNone && dropped.outcome.disposition == .forwardDrop &&
    dropped.state.handoff.gateways.primary == replied)
    "Actual current ordinary denial still marks an associated reply before filtering."
  let expired ← source wire.reverse 1
  let ttl ← probe ready ⟨.primary, .reply, expired, none⟩
  ensure (ttl.outcome.output.isNone && ttl.outcome.disposition == .ttlExpired && ttl.state.handoff.gateways.primary == replied)
    "Actual TTL rejection must preserve reply tracking and protected readiness without a postcheck assumption."

private def withdrawal (request reply : SafeHandoff.Source) : IO Unit := do
  let ready ← warm request
  let client ← operation ready (.handoff .client .standby)
  let server ← operation client (.handoff .server .standby)
  let pending ← operation server (.assign .reply reply)
  let fenced ← operation pending (.fence .primary)
  rejects fenced ⟨.primary, .reply, reply, none⟩ "The probe gateway is fenced."
  let withdrawn ← unwrap (CampusWithdrawal.step fenced .withdraw)
  rejects withdrawn.state ⟨.primary, .reply, reply, none⟩ "The primary probe target has been physically withdrawn."
  let result ← probe withdrawn.state ⟨.standby, .reply, reply, none⟩
  ensure (result.state.archive == some unreplied && result.state.handoff.gateways.primary == unreplied &&
    result.state.handoff.gateways.standby == replied && result.state.handoff.work.pending.map (·.id) == [0])
    "Live standby probes must preserve the historical primary archive and every outstanding legitimate ticket."

def run : IO Unit := do
  let request ← source original
  let reply ← source wire.reverse
  baseline request
  protectedProbes request reply
  withdrawal request reply

end NetlibTest.IngressProbe
