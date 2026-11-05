import Netlib.Protocol.SafeHandoffFacts

namespace NetlibTest.SafeHandoff

open Netlib Packet Protocol
namespace Model
export Netlib.Protocol.SafeHandoff (State Source Configuration Event Result Ticket PacketResult step contract Admissible)
end Model
open StatefulFailover (Gateway Leg)

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def payload : List UInt8 := [0, 255, 17, 0, 99]
private def routes : List (Routing.Entry String) :=
  [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
private def permit : ConntrackLifecycle.Pipeline := { routes, forward := [], forwardDefault := .permit }
private def deny : ConntrackLifecycle.Pipeline := { routes, forward := [] }
private def established : ConntrackLifecycle.Pipeline := { routes, forward := [ConntrackLifecycle.establishedPermit] }
private def configuration (id : String) (pipeline : ConntrackLifecycle.Pipeline) : Model.Configuration := ⟨id, pipeline⟩
private def initial : Model.State := .initial (configuration "primary" permit) (configuration "standby" permit)

example (trace : Model.contract.Trace before events after) (safe : before.Safe) :
    after.Safe ∧ ∀ event, Model.Admissible after event →
      ∃ result, Model.step after event = .ok result ∧ result.state.Safe :=
  Protocol.SafeHandoff.arbitrary_interleavings trace safe

example (before : Model.State) (gateway : Gateway) (safe : before.Safe) :
    ∃ (ids : List Nat) (after : Model.State),
      Model.contract.Trace before (ids.map Protocol.SafeHandoff.Event.serve) after ∧ after.Safe ∧
      after.outstanding gateway = 0 ∧ ids.length = before.outstanding gateway ∧
      after.gateways.owners = before.gateways.owners :=
  Protocol.SafeHandoff.drain_gateway before gateway safe

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def source (header : Header) (ttl : UInt8 := 64) : IO Model.Source := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨32, 4321, true, ttl, Packet.Protocol.udp, header.source, header.destination, transport⟩
  let bytes ← unwrap (IPv4.encode ip)
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw (IO.userError error)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def step (before : Model.State) (event : Model.Event) : IO Model.Result := do
  let result ← unwrap (Model.step before event)
  ensure result.state.check "An accepted operation must retain the executable protected-flow invariant."
  pure result

private def rejects (before : Model.State) (event : Model.Event) (expected : String) : IO Unit :=
  match Model.step before event with
  | .error message => ensure (message == expected) s!"Expected guard {expected}; got {message}."
  | .ok _ => throw (IO.userError "Expected the unsafe or unsupported operation to fail.")

private def establish (request : Model.Source) : IO Model.State := do
  let first ← step initial (.establish ⟨0, request.packet, some entry⟩)
  ensure (first.state.gateways.primary == unreplied && first.state.gateways.standby == .initial &&
    first.state.binding.isNone && first.established.isSome)
    "The protected binding must originate in actual primary packet processing."
  let staged ← step first.state (.stage 0 original)
  ensure (staged.state.binding == some entry && staged.state.gateways.cache.map (·.source) == some unreplied &&
    staged.state.gateways.cache.map (·.sourceEpoch) == some 1)
    "Staging must cite the actual primary prefix and selected binding."
  pure staged.state

private def ready (request : Model.Source) : IO Model.State := do
  let staged ← establish request
  let committed ← step staged (.commit 180)
  ensure (committed.state.gateways.primary == unreplied && committed.state.gateways.standby == unreplied)
    "Commit must warm standby before either endpoint route moves."
  pure committed.state

private def assign (before : Model.State) (direction : FlowNAT.Direction) (source : Model.Source)
    (id : Nat) (gateway : Gateway) : IO Model.State := do
  let result ← step before (.assign direction source)
  let some item := result.admitted | throw (IO.userError "Admission must return the actual new ticket.")
  ensure (item.id == id && item.value.gateway == gateway && item.value.direction == direction &&
    item.value.source.bytes == source.bytes && item.value.routeEpoch == before.gateways.epoch &&
    result.state.work.nextID == id + 1 && result.state.work.pending.map (·.id) == before.work.pending.map (·.id) ++ [id])
    "Admission must retain the actual bytes, route read, epoch, and unique pending ID."
  pure result.state

private def served (result : Model.Result) (id : Nat) (gateway : Gateway) (config : String)
    (direction : FlowNAT.Direction) (classification : StatefulACL.CTState)
    (disposition : WireForwarding.Disposition) : IO Unit := do
  let some packet := result.served | throw (IO.userError "Service must return its actual pending ticket.")
  ensure (packet.ticket.id == id && packet.ticket.value.gateway == gateway && packet.configuration.id == config &&
    packet.outcome.attachment.entry == entry && packet.outcome.attachment.direction == direction &&
    packet.outcome.attachment.classification == classification && !packet.outcome.attachment.fresh &&
    packet.outcome.disposition == disposition && !result.state.work.pending.any (·.id == id) &&
    result.state.work.completed.any (·.id == id))
    "Service must retire the selected ID using its assigned gateway and the current configuration and classification."
  match packet.outcome.output with
  | none => ensure (disposition != .forwarded) "Permitted routed live service must emit a packet."
  | some emission =>
    let expected := if direction == .original then translated else original.reverse
    ensure (disposition == .forwarded && emission.target == expected && emission.decoded.header == expected &&
      emission.decoded.datagram.payload == payload && emission.decoded.ip.packet.ttl == 63 &&
      emission.decoded.ip.packet.tos == 32 && emission.decoded.ip.packet.identification == 4321 &&
      emission.decoded.ip.packet.dontFragment)
      "Service must preserve the selected NAT boundary and payload while decrementing TTL exactly once."
    ensure ((← unwrap (UDP.decodeIPv4 emission.bytes)) == emission.decoded)
      "Emitted bytes must pass the independent IPv4 and UDP checksum decoders."

private def interleaving (request reply : Model.Source) (firstLeg : Leg) : IO Unit := do
  let warm ← ready request
  let oldOriginal ← assign warm .original request 0 .primary
  let oldBoth ← assign oldOriginal .reply reply 1 .primary
  let moved ← step oldBoth (.handoff firstLeg .standby)
  let firstDirection := if firstLeg == .client then FlowNAT.Direction.original else .reply
  let firstSource := if firstLeg == .client then request else reply
  let newTicket ← assign moved.state firstDirection firstSource 2 .standby
  let overtaking ← step newTicket (.serve 2)
  served overtaking 2 .standby "standby" firstDirection
    (if firstLeg == .client then .new else .established) .forwarded
  ensure (overtaking.state.work.pending.map (·.id) == [0, 1])
    "A later route ticket may complete before both earlier tickets."
  let secondDirection := if firstLeg == .client then FlowNAT.Direction.reply else .original
  let secondSource := if firstLeg == .client then reply else request
  let lastOld ← assign overtaking.state secondDirection secondSource 3 .primary
  let bothMoved ← step lastOld (.handoff (if firstLeg == .client then .server else .client) .standby)
  let newOriginal ← assign bothMoved.state .original request 4 .standby
  let newBoth ← assign newOriginal .reply reply 5 .standby
  rejects newBoth (.fence .primary) "Drain the gateway's outstanding route assignments before fencing it."
  let revoked ← step newBoth (.install .primary (configuration "revoked" deny))
  let deniedReply ← step revoked.state (.serve 1)
  served deniedReply 1 .primary "revoked" .reply .established .forwardDrop
  ensure (deniedReply.state.gateways.primary == replied && deniedReply.state.outstanding .primary == 2)
    "A denied old-route reply must still mark only the assigned primary record and drain one ticket."
  let current ← step deniedReply.state (.install .primary (configuration "current-established" established))
  let olderOriginal ← step current.state (.serve 0)
  served olderOriginal 0 .primary "current-established" .original .established .forwarded
  let finalOld ← step olderOriginal.state (.serve 3)
  served finalOld 3 .primary "current-established" secondDirection .established .forwarded
  ensure (finalOld.state.outstanding .primary == 0 && finalOld.state.outstanding .standby == 2 &&
    finalOld.state.gateways.owners.client == .standby && finalOld.state.gateways.owners.server == .standby)
    "Serving assigned old-route tickets must drain primary without changing current endpoint routes."
  let fenced ← step finalOld.state (.fence .primary)
  ensure (fenced.state.gateways.isFenced .primary && fenced.state.gateways.primary == replied)
    "Fencing after drain must retain the protected primary binding in the no-aging profile."
  let newReply ← step fenced.state (.serve 5)
  served newReply 5 .standby "standby" .reply .established .forwarded
  let newRequest ← step newReply.state (.serve 4)
  served newRequest 4 .standby "standby" .original .established .forwarded
  ensure (newRequest.state.work.pending.isEmpty && newRequest.state.work.completed.map (·.id) == [2, 1, 0, 3, 5, 4] &&
    newRequest.state.gateways.primary == replied && newRequest.state.gateways.standby == replied)
    "Arbitrary retirement order must retain exact ticket history and independent gateway reply observations."
  rejects newRequest.state (.serve 0) "The selected identity is not pending."
  rejects newRequest.state (.serve 99) "The selected identity is not pending."
  rejects newRequest.state (.handoff .client .primary) "The target route owner is fenced."

private def insertions (head : Nat) : List Nat → List (List Nat)
  | [] => [[head]]
  | first :: rest => (head :: first :: rest) :: (insertions head rest).map (first :: ·)

private def permutations : List Nat → List (List Nat)
  | [] => [[]]
  | head :: rest => (permutations rest).flatMap (insertions head)

private def arbitraryRetirement (request reply : Model.Source) : IO Unit := do
  let warm ← ready request
  let zero ← assign warm .original request 0 .primary
  let one ← assign zero .reply reply 1 .primary
  let two ← assign one .original request 2 .primary
  let three ← assign two .reply reply 3 .primary
  let client ← step three (.handoff .client .standby)
  let server ← step client.state (.handoff .server .standby)
  for ids in permutations [0, 1, 2, 3] do
    let mut current := server.state
    for id in ids do
      let beforeCount := current.outstanding .primary
      let result ← step current (.serve id)
      ensure (result.state.outstanding .primary + 1 == beforeCount && result.served.isSome)
        "Every selected actual primary ticket must retire exactly one outstanding assignment."
      current := result.state
    ensure (current.work.completed.map (·.id) == ids && current.work.pending.isEmpty)
      "All completion permutations must retain their actual retirement order."
    let fenced ← step current (.fence .primary)
    ensure (fenced.state.gateways.isFenced .primary)
      "Every complete retirement order must permit the final fence."

private def dropsAndGuards (request reply : Model.Source) : IO Unit := do
  rejects initial (.commit 180) "Stage the protected flow before kernel commitment."
  rejects initial (.assign .original request) "Stage the protected flow before route admission."
  rejects initial (.fence .primary) "Move both endpoint routes away before fencing a gateway."
  let staged ← establish request
  rejects staged (.handoff .client .standby) "The target gateway has no ready protected binding."
  rejects staged (.handoff .server .standby) "The target gateway has no ready protected binding."
  let warm ← ready request
  rejects warm (.commit 180) "Colliding native commit and destructive retry are outside this profile."
  rejects warm (.establish ⟨0, request.packet, some entry⟩)
    "Establishment precedes protected-flow staging and outstanding admissions."
  let other ← source { original with sourcePort := 41001 }
  rejects warm (.assign .original other) "The admission bytes do not identify the protected flow direction."
  for (pipeline, disposition, ttl) in [(deny, WireForwarding.Disposition.forwardDrop, (64 : UInt8)),
      ({ permit with lateDefault := .deny }, .lateDrop, 64),
      ({ permit with routes := [] }, .routeDrop, 64), (permit, .ttlExpired, 1), (permit, .ttlExpired, 0)] do
    let input ← source translated.reverse ttl
    let admitted ← assign warm .reply input 0 .primary
    let installed ← step admitted (.install .primary (configuration "drop" pipeline))
    let result ← step installed.state (.serve 0)
    served result 0 .primary "drop" .reply .established disposition
    ensure (result.state.gateways.primary == replied && result.state.work.pending.isEmpty &&
      Protocol.TrackedFlow.ready result.state.gateways.primary entry)
      "Policy, route, and TTL drops must retire pending work and preserve protected readiness."
  let pending ← assign warm .reply reply 0 .primary
  let forgotten ← step pending .forget
  ensure (forgotten.state.gateways.cache.isNone && forgotten.state.outstanding .primary == 1)
    "Forgetting replication cache must retain actual pending route tickets and confirmed bindings."
  let result ← step forgotten.state (.serve 0)
  served result 0 .primary "primary" .reply .established .forwarded

def run : IO Unit := do
  let request ← source original
  let reply ← source translated.reverse
  interleaving request reply .client
  interleaving request reply .server
  arbitraryRetirement request reply
  dropsAndGuards request reply

end NetlibTest.SafeHandoff
