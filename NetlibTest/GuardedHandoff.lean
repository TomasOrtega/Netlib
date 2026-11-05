import Netlib.Protocol.GuardedHandoff
import Netlib.Protocol.IngressAttachment
import Netlib.Packet.IngressPolicy

namespace NetlibTest.GuardedHandoff
open Netlib Packet Protocol
namespace Model
export Netlib.Protocol.GuardedHandoff (State Ticket Dropped Result retire serve)
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
private def session : EAPSession.State := EAPSession.run context .initial [
  .authentication .start, .authentication (.server (.request 1 13 [0x20])),
  .authentication (.peer (.response 1 13 [0])), .authentication (.server (.success 1)),
  .authentication (.method ⟨1, context.consumer, 13, true, some "selected method evidence"⟩),
  .application (.install credential)]

example (before : Model.State) (id : Nat) (safe : before.Safe)
    (pending : ∃ item ∈ before.handoff.work.pending, item.id = id) :
    ∃ dropped, Model.retire before id = .ok dropped :=
  Protocol.GuardedHandoff.retire_completes before id safe pending

example (before : Model.State) (id : Nat) (dropped : Model.Dropped before id) :
    dropped.state.handoff.gateways.primary = before.handoff.gateways.primary ∧
      dropped.state.handoff.gateways.standby = before.handoff.gateways.standby := dropped.tables_unchanged

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def source (header : Header) : IO SafeHandoff.Source := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let bytes ← unwrap (IPv4.encode ⟨32, 4321, false, 64, Packet.Protocol.udp, header.source, header.destination, transport⟩)
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw (IO.userError error)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def operation (before : Model.State) (event : SafeHandoff.Event) : IO Model.State := do
  let result ← unwrap (CampusWithdrawal.step before (.operation event))
  ensure result.state.check "The ordinary control operation must retain the withdrawal contract."
  pure result.state

private def warm (request : SafeHandoff.Source) : IO Model.State := do
  let established ← operation initial (.establish ⟨0, request.packet, some entry⟩)
  let staged ← operation established (.stage 0 original)
  operation staged (.commit 180)

private def queued (request reply : SafeHandoff.Source) : IO Model.State := do
  let before ← warm request
  let zero ← operation before (.assign .original request)
  let one ← operation zero (.assign .reply reply)
  let movedClient ← operation one (.handoff .client .standby)
  let two ← operation movedClient (.assign .original request)
  let movedServer ← operation two (.handoff .server .standby)
  operation movedServer (.assign .reply reply)

private def dropped (before : Model.State) (id : Nat) (gateway : Gateway) (actualDecision : Bool := false) : IO Model.State := do
  let result ← unwrap (Model.serve actualDecision before id)
  match result with
  | .processed _ _ => throw (IO.userError "An actual early rejection cannot fabricate an ordinary forwarding outcome.")
  | .rejected rejected =>
    ensure (rejected.state.check && rejected.ticket.id == id && rejected.ticket.value.gateway == gateway &&
      rejected.ticket.value.entry == entry &&
      rejected.state.handoff.gateways.primary == before.handoff.gateways.primary &&
      rejected.state.handoff.gateways.standby == before.handoff.gateways.standby &&
      rejected.state.handoff.gateways.cache.map (·.sourceEpoch) == before.handoff.gateways.cache.map (·.sourceEpoch) &&
      rejected.state.handoff.binding == before.handoff.binding &&
      rejected.state.handoff.gateways.owners.client == before.handoff.gateways.owners.client &&
      rejected.state.handoff.gateways.owners.server == before.handoff.gateways.owners.server &&
      rejected.state.handoff.gateways.fenced == before.handoff.gateways.fenced &&
      rejected.state.archive == before.archive && rejected.state.withdrawn == before.withdrawn &&
      rejected.state.handoff.work.nextID == before.handoff.work.nextID &&
      rejected.state.handoff.gateways.epoch == before.handoff.gateways.epoch + 1 &&
      rejected.state.handoff.work.completed.map (·.id) == before.handoff.work.completed.map (·.id) ++ [id] &&
      rejected.state.handoff.outstanding gateway + 1 == before.handoff.outstanding gateway)
      "Early rejection must retire the actual arbitrary identity while preserving complete tables, ownership, archive, allocation, and control metadata."
    ensure ((rejected.state.handoff.configurations .primary).id == "ordinary-permit" &&
      (rejected.state.handoff.configurations .standby).id == "ordinary-permit")
      "The ordinary forwarding policies must remain installed and permissive behind the early drop."
    pure rejected.state

private def processed (before : Model.State) (id : Nat) (gateway : Gateway) (direction : FlowNAT.Direction)
    (actualDecision : Bool := true) : IO Model.State := do
  let result ← unwrap (Model.serve actualDecision before id)
  match result with
  | .rejected _ => throw (IO.userError "An actual permit must delegate to the ordinary handoff operation.")
  | .processed operated _ =>
    let some parent := operated.operation | throw (IO.userError "Expected the computed handoff result.")
    let some served := parent.served | throw (IO.userError "Expected actual ordinary packet processing.")
    let some output := served.outcome.output | throw (IO.userError "The permissive routed live packet must emit.")
    let target := if direction == .original then wire else original.reverse
    ensure (served.ticket.id == id && served.ticket.value.gateway == gateway && served.ticket.value.direction == direction &&
      output.decoded.header == target && output.decoded.datagram.payload == payload && output.decoded.ip.packet.ttl == 63)
      "Actual permits must retain ordinary NAT, payload, TTL, and assigned-ticket behavior."
    ensure ((← unwrap (UDP.decodeIPv4 output.bytes)) == output.decoded)
      "The delegated emission must retain valid IPv4 and UDP checksum bytes."
    pure operated.state

private def insertions (head : Nat) : List Nat → List (List Nat)
  | [] => [[head]]
  | first :: rest => (head :: first :: rest) :: (insertions head rest).map (first :: ·)
private def permutations : List Nat → List (List Nat)
  | [] => [[]]
  | head :: rest => (permutations rest).flatMap (insertions head)

private def rejectionOrders (request reply : SafeHandoff.Source) : IO Unit := do
  let before ← queued request reply
  ensure (before.handoff.work.pending.map (·.id) == [0, 1, 2, 3]) "Four actual assignments must precede the retirement-order experiment."
  for order in permutations [0, 1, 2, 3] do
    let mut state := before
    for id in order do
      state ← dropped state id (if id < 2 then .primary else .standby)
    ensure (state.handoff.work.pending.isEmpty && state.handoff.work.completed.map (·.id) == order &&
      state.handoff.gateways.primary == unreplied && state.handoff.gateways.standby == unreplied)
      "Every rejection order must preserve exact history and both unreplied records without entering ordinary tracking."
    let fenced ← operation state (.fence .primary)
    let withdrawn ← unwrap (CampusWithdrawal.step fenced .withdraw)
    ensure (withdrawn.state.withdrawn && withdrawn.state.archive == some unreplied)
      "Exact retirement counts must enable fencing and archival withdrawal in every completion order."

private def logoffTimeline (request reply : SafeHandoff.Source) : IO Unit := do
  let before ← queued request reply
  let overtaking ← processed before 2 .standby .original
  ensure (session.session.permits context scope) "The declared current session must initially permit its application scope."
  let loggedOff := EAPSession.step context session (.authentication .logoff)
  ensure (!(loggedOff.session.permits context scope)) "Logoff must remove current desired session permission."
  let installedGuard : Packet.IngressPolicy.Policy := {}
  ensure (!(installedGuard.allows 2 original) && !(installedGuard.allows 3 wire.reverse))
    "The explicitly installed early guard must reject both application directions."
  let counterfactual ← processed overtaking 1 .primary .reply
  ensure (counterfactual.handoff.gateways.primary == replied)
    "The retained ordinary permit would update seen-reply state if the early guard were bypassed."
  let oldReply ← dropped overtaking 1 .primary (installedGuard.allows 3 wire.reverse)
  let oldOriginal ← dropped oldReply 0 .primary (installedGuard.allows 2 original)
  let fenced ← operation oldOriginal (.fence .primary)
  let withdrawn ← unwrap (CampusWithdrawal.step fenced .withdraw)
  let lastReply ← dropped withdrawn.state 3 .standby (installedGuard.allows 3 wire.reverse)
  ensure (lastReply.archive == some unreplied && lastReply.handoff.gateways.primary == unreplied &&
    lastReply.handoff.gateways.standby == unreplied && lastReply.handoff.work.completed.map (·.id) == [2, 1, 0, 3])
    "Postwithdrawal early rejection must preserve the historical primary and the live standby's ordinary state."
  for id in [0, 3, 99] do
    match Model.serve false lastReply id with
    | .error "The selected identity is not pending." => pure ()
    | _ => throw (IO.userError "Retired or unallocated identities cannot be rejected again.")
  let staleRequest ← operation lastReply (.assign .original request)
  let staleGuard : Packet.IngressPolicy.Policy := { fallback := .permit }
  let staleProcessed ← processed staleRequest 4 .standby .original (staleGuard.allows 2 original)
  ensure (!(loggedOff.session.permits context scope) && staleProcessed.handoff.gateways.standby == unreplied)
    "A supplied stale actual permit must execute ordinary processing despite desired session denial, leaving mismatch reporting to the caller."
  let pendingReply ← operation staleProcessed (.assign .reply reply)
  let final ← dropped pendingReply 5 .standby (installedGuard.allows 3 wire.reverse)
  ensure (final.handoff.gateways.standby == unreplied && final.archive == some unreplied)
    "Rejected cached replies must never mark seen-reply state, including after continued ordinary traffic and archival withdrawal."
  let invalid := { final with handoff := { final.handoff with
    gateways := { final.handoff.gateways with standby := ⟨[⟨entry, false⟩, ⟨entry, true⟩]⟩ } } }
  match Model.retire invalid 99 with
  | .error "The guarded handoff state violates its contract." => pure ()
  | _ => throw (IO.userError "An invalid before-state cannot acquire a rejection safety certificate.")

def run : IO Unit := do
  let request ← source original
  let reply ← source wire.reverse
  rejectionOrders request reply
  logoffTimeline request reply

end NetlibTest.GuardedHandoff
